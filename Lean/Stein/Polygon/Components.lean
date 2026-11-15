import Stein.Polygon.Rays

/-!
# The two sides of a simple closed polygonal curve

Let `v : ι → ℝ × ℝ` and `σ : ι ≃ ι` describe a simple closed polygonal curve (`Simple v σ`, sides
`v k → v (σ k)`, curve `curveCyc v σ`).  This file proves that every point off the curve can be
joined, inside the complement of the curve, to one of two fixed points; hence the complement has
at most two connected components.  This is the main step of the polygonal Jordan curve theorem
of `Stein/Polygon/Jordan.lean`.

* `Joined v σ x y` : `x` and `y` lie in a connected subset of the complement of the curve.
* `SideOf v σ e k t x` : `x` is joined to the points close to the point `pt (v k) (v (σ k)) t` of
  the side `k`, on its left (`e > 0`) or on its right (`e < 0`).
* `sector` : near a vertex the complement of the curve is covered by two connected sets
  (two sectors, in polar coordinates).
* `two_sides` : there are two points `xL`, `xR` off the curve such that every point off the curve
  is joined to `xL` or to `xR`.
* `isPreconnected_wind_eq` : the set of the points off the curve with a given winding number is
  connected.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- `x` and `y` lie in a connected set which does not meet the curve -/
def Joined (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (x y : ℝ × ℝ) : Prop :=
  ∃ S : Set (ℝ × ℝ), IsPreconnected S ∧ S ⊆ (curveCyc v σ)ᶜ ∧ x ∈ S ∧ y ∈ S

omit [Fintype ι] in
/-- `Joined` is symmetric. -/
theorem Joined.symm {x y : ℝ × ℝ} (h : Joined v σ x y) : Joined v σ y x := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  exact ⟨S, h1, h2, h4, h3⟩

omit [Fintype ι] in
/-- `Joined` is transitive. -/
theorem Joined.trans {x y z : ℝ × ℝ} (h : Joined v σ x y) (h' : Joined v σ y z) :
    Joined v σ x z := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  obtain ⟨S', h1', h2', h3', h4'⟩ := h'
  exact ⟨S ∪ S', IsPreconnected.union y h4 h3' h1 h1', union_subset h2 h2', Or.inl h3, Or.inr h4'⟩

/-- Joined points have the same winding number. -/
theorem Joined.wind_eq {x y : ℝ × ℝ} (h : Joined v σ x y) : wind v σ x = wind v σ y := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  exact wind_const_on h1 h2 h3 h4

omit [Fintype ι] in
/-- Two points of a connected set which does not meet the curve are joined. -/
theorem Joined.of_mem {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSU : S ⊆ (curveCyc v σ)ᶜ)
    {x y : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) : Joined v σ x y := ⟨S, hS, hSU, hx, hy⟩

/-- `x` is joined to the points near `pt (v k) (v (σ k)) t` on the left (`e > 0`) or on the right
(`e < 0`) of the side `k` -/
def SideOf (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (e : ℝ) (k : ι) (t : ℝ) (x : ℝ × ℝ) : Prop :=
  ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t), 0 < e * cross (v k) (v (σ k)) y → Joined v σ x y

/-- `cross a b` is an affine function. -/
private theorem cross_combo (a b y y' : ℝ × ℝ) (s s' : ℝ) (h : s + s' = 1) :
    cross a b (s • y + s' • y') = s * cross a b y + s' * cross a b y' := by
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) * h

/-- An open half-plane bounded by the line `a b` is convex. -/
private theorem convex_side (a b : ℝ × ℝ) (e : ℝ) : Convex ℝ {y | 0 < e * cross a b y} := by
  intro y hy y' hy' s s' hs hs' hss
  simp only [mem_ofPred_eq] at hy hy' ⊢
  rw [cross_combo a b y y' s s' hss]
  rcases hs.lt_or_eq with h | h
  · nlinarith [mul_pos h hy, mul_nonneg hs' hy'.le]
  · have : s' = 1 := by linarith
    rw [← h, this]; linarith

/-- Every point of the line `a b` is a limit of points strictly on its left (`e > 0`) and of
points strictly on its right (`e < 0`). -/
theorem freq_side {a b x : ℝ × ℝ} (hab : a ≠ b) (hx : cross a b x = 0) {e : ℝ} (he : e ≠ 0) :
    ∃ᶠ y in 𝓝 x, 0 < e * cross a b y := by
  obtain ⟨f1, f2⟩ := frequently_cross hab hx
  rcases lt_or_gt_of_ne he with h | h
  · exact f1.mono (fun y hy => mul_pos_of_neg_of_neg h hy)
  · exact f2.mono (fun y hy => mul_pos h hy)

/-- The points `pt a b t` lie on the line `a b`. -/
theorem cross_pt (a b : ℝ × ℝ) (t : ℝ) : cross a b (pt a b t) = 0 := by
  simp only [cross, pt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- the points near a point of a side, on one side of it, are joined to each other -/
private theorem half_ball (hs : Simple v σ) (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (e : ℝ) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t), 0 < e * cross (v k) (v (σ k)) y → SideOf v σ e k t y := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_off_others hs k ht)
  set C : Set (ℝ × ℝ) := Metric.ball (pt (v k) (v (σ k)) t) r ∩
    {y | 0 < e * cross (v k) (v (σ k)) y} with hC
  have hconv : Convex ℝ C := (convex_ball _ _).inter (convex_side _ _ e)
  have hCU : C ⊆ (curveCyc v σ)ᶜ := by
    rintro y ⟨hy1, hy2⟩ hmem
    obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
    by_cases hjk : j = k
    · rw [hjk] at hj
      simp only [mem_ofPred_eq, cross_of_mem_segment hj, mul_zero, lt_self_iff_false] at hy2
    · exact hball y hy1 j hjk hj
  filter_upwards [Metric.ball_mem_nhds _ hr] with y hyB hy
  unfold SideOf
  filter_upwards [Metric.ball_mem_nhds _ hr] with y' hyB' hy'
  exact Joined.of_mem hconv.isPreconnected hCU ⟨hyB, hy⟩ ⟨hyB', hy'⟩

omit [Fintype ι] in
/-- Two points on the same side of a side are joined. -/
theorem SideOf.join (hs : Simple v σ) {e : ℝ} (he : e ≠ 0) {k : ι} {t : ℝ} {x x' : ℝ × ℝ}
    (h : SideOf v σ e k t x) (h' : SideOf v σ e k t x') : Joined v σ x x' := by
  obtain ⟨y, hy, h1, h2⟩ :=
    ((freq_side (hs.ne k) (cross_pt _ _ t) he).and_eventually (h.and h')).exists
  exact (h1 hy).trans (h2 hy).symm

omit [Fintype ι] in
/-- A point joined to a point on one side of a side is on the same side of it. -/
theorem SideOf.of_joined {e : ℝ} {k : ι} {t : ℝ} {x x' : ℝ × ℝ}
    (h : SideOf v σ e k t x) (h' : Joined v σ x x') : SideOf v σ e k t x' :=
  h.mono (fun _ hy hc => h'.symm.trans (hy hc))

omit [Fintype ι] in
/-- `SideOf v σ e k t x` is an open condition on the parameter `t`. -/
theorem SideOf.open {e : ℝ} {k : ι} {t : ℝ} {x : ℝ × ℝ} (h : SideOf v σ e k t x) :
    ∀ᶠ t' in 𝓝 t, SideOf v σ e k t' x :=
  (continuous_pt (v k) (v (σ k))).continuousAt.eventually (eventually_eventually_nhds.2 h)

/-- Every side has points on each of its two sides. -/
private theorem exists_sideOf (hs : Simple v σ) (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {e : ℝ}
    (he : e ≠ 0) : ∃ x, SideOf v σ e k t x := by
  obtain ⟨y, hy, h1⟩ :=
    ((freq_side (hs.ne k) (cross_pt _ _ t) he).and_eventually (half_ball hs k ht e)).exists
  exact ⟨y, h1 hy⟩

/-- `SideOf` does not depend on the point of the side -/
theorem SideOf.const (hs : Simple v σ) {e : ℝ} (he : e ≠ 0) {k : ι} {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1) {x : ℝ × ℝ} (h : SideOf v σ e k t x) :
    SideOf v σ e k t' x := by
  classical
  have hloc : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ᶠ s' in 𝓝 s, (SideOf v σ e k s' x ↔ SideOf v σ e k s x) := by
    intro s hs'
    by_cases hx : SideOf v σ e k s x
    · filter_upwards [hx.open] with s' h'
      exact ⟨fun _ => hx, fun _ => h'⟩
    · obtain ⟨x₀, hx₀⟩ := exists_sideOf hs k hs' he
      filter_upwards [hx₀.open] with s' h'
      refine ⟨fun h1 => hx₀.of_joined (h'.join hs he h1), fun h1 => absurd h1 hx⟩
  have hcont : ContinuousOn (fun s => decide (SideOf v σ e k s x)) (Ioo (0 : ℝ) 1) := by
    intro s hs'
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.congr
    filter_upwards [hloc s hs'] with s' h'
    show decide (SideOf v σ e k s x) = decide (SideOf v σ e k s' x)
    simp only [h']
  have := isPreconnected_Ioo.constant hcont ht ht'
  simpa [h] using this.symm

/-! ### The neighbourhood of a vertex: two sectors -/

/-- the inverse of `toC` -/
private def fromC (z : ℂ) : ℝ × ℝ := (z.re, z.im)

/-- `fromC` is a right inverse of `toC`. -/
private theorem toC_fromC (z : ℂ) : toC (fromC z) = z := by
  apply Complex.ext <;> simp [toC, fromC]

/-- `fromC` is a left inverse of `toC`. -/
private theorem fromC_toC (p : ℝ × ℝ) : fromC (toC p) = p := by
  apply Prod.ext <;> simp [toC, fromC]

/-- `fromC` is continuous. -/
private theorem continuous_fromC : Continuous fromC := by unfold fromC; fun_prop

/-- `toC` does not decrease distances. -/
private theorem dist_le_norm_toC (y p : ℝ × ℝ) : dist y p ≤ ‖toC y - toC p‖ := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  apply max_le
  · have := Complex.abs_re_le_norm (toC y - toC p)
    simpa [toC] using this
  · have := Complex.abs_im_le_norm (toC y - toC p)
    simpa [toC] using this

/-- **near a vertex, the complement of the curve is covered by two connected sets** -/
theorem sector (hs : Simple v σ) (k : ι) :
    ∃ S1 S2 : Set (ℝ × ℝ), IsPreconnected S1 ∧ IsPreconnected S2 ∧
      S1 ⊆ (curveCyc v σ)ᶜ ∧ S2 ⊆ (curveCyc v σ)ᶜ ∧
      ∀ᶠ y in 𝓝 (v (σ k)), y ∉ curveCyc v σ → y ∈ S1 ∨ y ∈ S2 := by
  classical
  set a := v k with ha
  set p := v (σ k) with hp
  set b := v (σ (σ k)) with hb
  set w : ℂ := toC a - toC p with hw
  have hw0 : w ≠ 0 := toC_sub_ne (hs.ne k)
  set z₀ : ℂ := -(toC b - toC p) / w with hz₀
  have hz₀' : z₀ = (toC b - toC p) / (toC p - toC a) := by
    rw [hz₀, hw, neg_div, ← div_neg, neg_sub]
  have hslit : z₀ ∈ slitPlane := by rw [hz₀']; exact hs.turn_slit k
  have hz₀0 : z₀ ≠ 0 := slitPlane_ne_zero hslit
  have hwz₀ : w * z₀ = -(toC b - toC p) := by rw [hz₀]; field_simp
  set θ₀ := arg z₀ with hθ₀
  have hθ₀π : θ₀ ≠ Real.pi := (mem_slitPlane_iff_arg.1 hslit).1
  -- the other sides are far from `p`
  have hoth : ∀ᶠ y in 𝓝 p, ∀ j, j ≠ k → j ≠ σ k → y ∉ segment ℝ (v j) (v (σ j)) := by
    apply eventually_all.2
    intro j
    by_cases hj : j ≠ k ∧ j ≠ σ k
    · have hjm : j ∈ (Finset.univ.erase k).erase (σ k) :=
        Finset.mem_erase.2 ⟨hj.2, Finset.mem_erase.2 ⟨hj.1, Finset.mem_univ _⟩⟩
      exact (eventually_notMem_segment (hs.vertex_not_mem k hjm)).mono (fun y hy _ _ => hy)
    · apply Eventually.of_forall
      intro y h1 h2
      exact absurd ⟨h1, h2⟩ hj
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hoth
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hz₀n : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀0
  set ρ : ℝ := min (min 1 ‖z₀‖) (δ / ‖w‖) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min one_pos hz₀n) (div_pos hδ hwn)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hρz : ρ ≤ ‖z₀‖ := (min_le_left _ _).trans (min_le_right _ _)
  have hρδ : ρ * ‖w‖ ≤ δ := by
    have := min_le_right (min 1 ‖z₀‖) (δ / ‖w‖)
    exact (le_div_iff₀ hwn).1 this
  set Φ : ℝ × ℝ → ℝ × ℝ := fun q => fromC (toC p - w * (q.1 * exp (q.2 * I))) with hΦ
  have hΦc : Continuous Φ := by
    apply continuous_fromC.comp
    fun_prop
  -- points of the two sectors are off the curve
  have hoff : ∀ r θ : ℝ, r ∈ Ioo 0 ρ → θ ∈ Ioo (-Real.pi) Real.pi → θ ≠ θ₀ →
      Φ (r, θ) ∉ curveCyc v σ := by
    intro r θ hr hθ hne hmem
    set z : ℂ := r * exp (θ * I) with hz
    have hz0 : z ≠ 0 := mul_ne_zero (by exact_mod_cast hr.1.ne') (exp_ne_zero _)
    have hargz : arg z = θ := by
      rw [hz, arg_real_mul _ hr.1, exp_mul_I]
      exact arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩
    have hy : toC (Φ (r, θ)) - toC p = -(w * z) := by
      simp only [hΦ, toC_fromC, hz]; ring
    obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
    by_cases hjk : j = k
    · rw [hjk, segment_eq_pt] at hj
      obtain ⟨τ, hτ, e⟩ := hj
      have e' := congrArg toC e
      rw [toC_pt] at e'
      have h1 : w * z = w * ((τ - 1 : ℝ) : ℂ) := by
        have : -(w * z) = toC (v k) + τ * (toC (v (σ k)) - toC (v k)) - toC p := by
          rw [← hy, ← e']
        rw [neg_eq_iff_eq_neg] at this
        rw [this, hw, hp, ha]; push_cast; ring
      have h2 : z = ((τ - 1 : ℝ) : ℂ) := mul_left_cancel₀ hw0 h1
      rcases (sub_nonpos.2 hτ.2).lt_or_eq with h | h
      · have : arg z = Real.pi := by rw [h2]; exact arg_ofReal_of_neg h
        rw [hargz] at this
        exact hθ.2.ne this
      · rw [h] at h2
        exact hz0 (by rw [h2]; simp)
    by_cases hjk' : j = σ k
    · rw [hjk', segment_eq_pt] at hj
      obtain ⟨τ, hτ, e⟩ := hj
      have e' := congrArg toC e
      rw [toC_pt] at e'
      have h1 : w * z = w * ((τ : ℂ) * z₀) := by
        have : -(w * z) = toC (v (σ k)) + τ * (toC (v (σ (σ k))) - toC (v (σ k))) - toC p := by
          rw [← hy, ← e']
        rw [neg_eq_iff_eq_neg] at this
        rw [this, ← mul_assoc, mul_comm w, mul_assoc, hwz₀, hp, hb]; ring
      have h2 : z = (τ : ℂ) * z₀ := mul_left_cancel₀ hw0 h1
      rcases hτ.1.lt_or_eq with h | h
      · have : arg z = θ₀ := by rw [h2, arg_real_mul _ h]
        rw [hargz] at this
        exact hne this
      · rw [← h] at h2
        exact hz0 (by rw [h2]; simp)
    · apply hball (Φ (r, θ)) _ j hjk hjk' hj
      rw [Metric.mem_ball]
      apply lt_of_le_of_lt (dist_le_norm_toC _ _)
      rw [hy, norm_neg, norm_mul, hz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1, norm_exp_ofReal_mul_I, mul_one]
      calc ‖w‖ * r < ‖w‖ * ρ := mul_lt_mul_of_pos_left hr.2 hwn
        _ = ρ * ‖w‖ := mul_comm _ _
        _ ≤ δ := hρδ
  refine ⟨Φ '' (Ioo 0 ρ ×ˢ Ioo (-Real.pi) θ₀), Φ '' (Ioo 0 ρ ×ˢ Ioo θ₀ Real.pi),
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ hΦc.continuousOn,
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ hΦc.continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    exact hoff r θ hr ⟨hθ.1, hθ.2.trans (lt_of_le_of_ne (arg_le_pi _) hθ₀π)⟩ hθ.2.ne
  · rintro _ ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    exact hoff r θ hr ⟨(neg_pi_lt_arg _).trans hθ.1, hθ.2⟩ hθ.1.ne'
  · set zf : ℝ × ℝ → ℂ := fun y => -(toC y - toC p) / w with hzf
    have hzfc : Continuous zf := by
      have := continuous_toC
      fun_prop
    have hzfp : zf p = 0 := by simp [hzf]
    have hev : ∀ᶠ y in 𝓝 p, ‖zf y‖ < ρ := by
      have h1 : ContinuousAt (fun y => ‖zf y‖) p := hzfc.norm.continuousAt
      exact h1.eventually_lt_const (by show ‖zf p‖ < ρ; rw [hzfp, norm_zero]; exact hρ0)
    filter_upwards [hev] with y hy hyc
    set z := zf y with hz
    have hyz : toC y = toC p - w * z := by
      rw [hz, hzf]; field_simp; ring
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at hyz
      apply hyc
      rw [toC_inj.1 hyz]
      exact mem_iUnion.2 ⟨k, right_mem_segment ℝ _ _⟩
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have h1 : arg z ≠ Real.pi := by
      intro h
      obtain ⟨hre, him⟩ := arg_eq_pi_iff.1 h
      have hzr : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
      have hnr : -z.re < ρ := by
        have := Complex.abs_re_le_norm z
        rw [abs_of_neg hre] at this
        linarith
      apply hyc
      refine mem_iUnion.2 ⟨k, ?_⟩
      rw [segment_symm, segment_eq_pt]
      refine ⟨-z.re, ⟨by linarith, by linarith⟩, ?_⟩
      apply toC_inj.1
      have hyz' : toC y = toC p - w * ((z.re : ℝ) : ℂ) := by rw [← hzr]; exact hyz
      rw [toC_pt, hyz', hw]
      simp only [ha, hp]
      push_cast; ring
    have h2 : arg z ≠ θ₀ := by
      intro h
      have e := (arg_eq_arg_iff hz₀0 hz0).1 h.symm
      apply hyc
      refine mem_iUnion.2 ⟨σ k, ?_⟩
      rw [segment_eq_pt]
      refine ⟨‖z‖ / ‖z₀‖, ⟨by positivity, (div_le_one hz₀n).2 (hy.le.trans hρz)⟩, ?_⟩
      apply toC_inj.1
      have hyz' : toC y = toC p - w * ((‖z‖ / ‖z₀‖ : ℂ) * z₀) := by rw [e]; exact hyz
      rw [toC_pt, hyz', ← mul_assoc, mul_comm w, mul_assoc, hwz₀]
      simp only [hp, hb]
      push_cast; ring
    have hΦy : Φ (‖z‖, arg z) = y := by
      simp only [hΦ]
      rw [norm_mul_exp_arg_mul_I, ← hyz, fromC_toC]
    have hpi : arg z < Real.pi := lt_of_le_of_ne (arg_le_pi _) h1
    rcases lt_or_gt_of_ne h2 with h | h
    · left
      exact ⟨(‖z‖, arg z), ⟨⟨hzn, hy⟩, ⟨neg_pi_lt_arg _, h⟩⟩, hΦy⟩
    · right
      exact ⟨(‖z‖, arg z), ⟨⟨hzn, hy⟩, ⟨h, hpi⟩⟩, hΦy⟩

/-! ### Walking along the curve -/

/-- the winding number near a side: `l` on its left, `l - 1` on its right -/
def sideWind (l : ℤ) (e : ℝ) : ℤ := if 0 < e then l else l - 1

/-- The winding numbers on the two sides of a side are different. -/
private theorem sideWind_ne (l : ℤ) {e : ℝ} (he : e ≠ 0) : sideWind l e ≠ sideWind l (-e) := by
  unfold sideWind
  rcases lt_or_gt_of_ne he with h | h
  · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left (by linarith)]; omega
  · rw [ite_eq_left h, ite_eq_right (by linarith)]; omega

/-- Near a point of a side (not an end point), the points strictly on one side of it are off
the curve, on that side of the side in the sense of `SideOf`, and have winding number
`sideWind l e`. -/
theorem side_witness (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {e : ℝ} (he : e ≠ 0) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t), 0 < e * cross (v k) (v (σ k)) y →
      y ∉ curveCyc v σ ∧ SideOf v σ e k t y ∧ wind v σ y = sideWind l e := by
  filter_upwards [half_ball hs k ht e, eventually_off_others hs k ht,
    wind_jump v σ k (hs.ne k) ht.1 ht.2 (hs.pt_not_mem k ht.1 ht.2)] with y h1 h2 h3 hc
  refine ⟨?_, h1 hc, ?_⟩
  · intro hmem
    obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
    by_cases hjk : j = k
    · rw [hjk] at hj
      rw [cross_of_mem_segment hj, mul_zero] at hc
      exact lt_irrefl _ hc
    · exact h2 j hjk hj
  · rw [hl k t ht] at h3
    unfold sideWind
    rcases lt_or_gt_of_ne he with h | h
    · rw [ite_eq_right (not_lt.2 h.le)]
      apply h3.2
      by_contra hcn
      have := mul_nonpos_of_nonpos_of_nonneg h.le (not_lt.1 hcn)
      linarith
    · rw [ite_eq_left h]
      apply h3.1
      by_contra hcn
      have := mul_nonpos_of_nonneg_of_nonpos h.le (not_lt.1 hcn)
      linarith

/-- There are points as in `side_witness` satisfying any property which holds near the point
of the side. -/
private theorem exists_witness (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {e : ℝ} (he : e ≠ 0) {P : ℝ × ℝ → Prop}
    (hP : ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t), P y) :
    ∃ y, P y ∧ y ∉ curveCyc v σ ∧ SideOf v σ e k t y ∧ wind v σ y = sideWind l e := by
  obtain ⟨y, hy, h1, h2⟩ := ((freq_side (hs.ne k) (cross_pt _ _ t) he).and_eventually
    ((side_witness hs hl k ht he).and hP)).exists
  exact ⟨y, h2, h1 hy⟩

/-- **passing a vertex**: the left (right) side of a side is joined to the left (right) side of
the next side -/
theorem SideOf.next (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    {e : ℝ} (he : e ≠ 0) {k : ι} {t t' : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    {x : ℝ × ℝ} (h : SideOf v σ e k t x) : SideOf v σ e (σ k) t' x := by
  obtain ⟨S1, S2, hS1, hS2, hU1, hU2, hcov⟩ := sector hs k
  have hcov' := eventually_eventually_nhds.2 hcov
  have ht1 : Tendsto (pt (v k) (v (σ k))) (𝓝[<] 1) (𝓝 (v (σ k))) := by
    have := (continuous_pt (v k) (v (σ k))).tendsto 1
    rw [pt_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs1, hs2⟩ := ((ht1.eventually hcov').and (Ioo_mem_nhdsLT zero_lt_one)).exists
  have ht0 : Tendsto (pt (v (σ k)) (v (σ (σ k)))) (𝓝[>] 0) (𝓝 (v (σ k))) := by
    have := (continuous_pt (v (σ k)) (v (σ (σ k)))).tendsto 0
    rw [pt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s', hs1', hs2'⟩ := ((ht0.eventually hcov').and (Ioo_mem_nhdsGT zero_lt_one)).exists
  obtain ⟨y, hyP, hyc, hyS, hyw⟩ := exists_witness hs hl k hs2 he hs1
  obtain ⟨y', hyP', hyc', -, hyw'⟩ := exists_witness hs hl k hs2 (neg_ne_zero.2 he) hs1
  obtain ⟨z, hzP, hzc, hzS, hzw⟩ := exists_witness hs hl (σ k) hs2' he hs1'
  have hne := sideWind_ne l he
  have hyz : Joined v σ y z := by
    rcases hyP hyc with h1 | h1 <;> rcases hzP hzc with h2 | h2
    · exact Joined.of_mem hS1 hU1 h1 h2
    · exfalso
      rcases hyP' hyc' with h3 | h3
      · exact hne (by rw [← hyw, ← hyw']; exact wind_const_on hS1 hU1 h1 h3)
      · exact hne (by rw [← hzw, ← hyw']; exact wind_const_on hS2 hU2 h2 h3)
    · exfalso
      rcases hyP' hyc' with h3 | h3
      · exact hne (by rw [← hzw, ← hyw']; exact wind_const_on hS1 hU1 h2 h3)
      · exact hne (by rw [← hyw, ← hyw']; exact wind_const_on hS2 hU2 h1 h3)
    · exact Joined.of_mem hS2 hU2 h1 h2
  have h1 : Joined v σ x y := (h.const hs he ht hs2).join hs he hyS
  exact (hzS.of_joined (h1.trans hyz).symm).const hs he hs2' ht'

/-- there is a point which is on the left (right) of all sides -/
theorem SideOf.all (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    {e : ℝ} (he : e ≠ 0) :
    ∃ x, x ∉ curveCyc v σ ∧ wind v σ x = sideWind l e ∧
      ∀ k t, t ∈ Ioo (0 : ℝ) 1 → SideOf v σ e k t x := by
  obtain ⟨i₀, hcyc⟩ := hs.cyc
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨x, -, hxc, hxS, hxw⟩ := exists_witness hs hl i₀ hhalf he (P := fun _ => True)
    (Eventually.of_forall (fun _ => trivial))
  refine ⟨x, hxc, hxw, ?_⟩
  apply hcyc
  · intro t ht; exact hxS.const hs he hhalf ht
  · intro i hi t ht; exact (hi _ hhalf).next hs hl he hhalf ht

/-! ### Far points -/

/-- the complement of a box containing the vertices is connected and does not meet the region -/
private theorem exists_far_set (v : ι → ℝ × ℝ) (σ : ι ≃ ι) :
    ∃ F : Set (ℝ × ℝ), IsPreconnected F ∧ Bornology.IsBounded Fᶜ ∧ F ⊆ (regionCyc v σ)ᶜ := by
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range v
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range v
  have hsub := regionCyc_subset_Icc σ lo hi
    (fun j => ⟨hlo (mem_range_self j), hhi (mem_range_self j)⟩)
  have c1 : Convex ℝ {y : ℝ × ℝ | y.1 < lo.1} :=
    (convex_Iio lo.1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have c2 : Convex ℝ {y : ℝ × ℝ | y.2 < lo.2} :=
    (convex_Iio lo.2).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  have c3 : Convex ℝ {y : ℝ × ℝ | hi.1 < y.1} :=
    (convex_Ioi hi.1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  have c4 : Convex ℝ {y : ℝ × ℝ | hi.2 < y.2} :=
    (convex_Ioi hi.2).linear_preimage (LinearMap.snd ℝ ℝ ℝ)
  have p12 : IsPreconnected ({y : ℝ × ℝ | y.1 < lo.1} ∪ {y : ℝ × ℝ | y.2 < lo.2}) :=
    IsPreconnected.union (lo.1 - 1, lo.2 - 1) (show lo.1 - 1 < lo.1 by linarith)
      (show lo.2 - 1 < lo.2 by linarith) c1.isPreconnected c2.isPreconnected
  have p123 : IsPreconnected ({y : ℝ × ℝ | y.1 < lo.1} ∪ {y : ℝ × ℝ | y.2 < lo.2} ∪
      {y : ℝ × ℝ | hi.1 < y.1}) :=
    IsPreconnected.union (hi.1 + 1, lo.2 - 1) (Or.inr (show lo.2 - 1 < lo.2 by linarith))
      (show hi.1 < hi.1 + 1 by linarith) p12 c3.isPreconnected
  have p : IsPreconnected ({y : ℝ × ℝ | y.1 < lo.1} ∪ {y : ℝ × ℝ | y.2 < lo.2} ∪
      {y : ℝ × ℝ | hi.1 < y.1} ∪ {y : ℝ × ℝ | hi.2 < y.2}) :=
    IsPreconnected.union (hi.1 + 1, hi.2 + 1) (Or.inr (show hi.1 < hi.1 + 1 by linarith))
      (show hi.2 < hi.2 + 1 by linarith) p123 c4.isPreconnected
  refine ⟨_, p, ?_, ?_⟩
  · apply (Metric.isBounded_Icc lo hi).subset
    intro y hy
    by_contra hbox
    apply hy
    by_contra hn
    apply hbox
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · by_contra h; exact hn (Or.inl (Or.inl (Or.inl (not_le.1 h))))
    · by_contra h; exact hn (Or.inl (Or.inl (Or.inr (not_le.1 h))))
    · by_contra h; exact hn (Or.inl (Or.inr (not_le.1 h)))
    · by_contra h; exact hn (Or.inr (not_le.1 h))
  · intro y hy hreg
    have hbox := hsub hreg
    rcases hy with ((h | h) | h) | h
    · exact absurd hbox.1.1 (not_le.2 h)
    · exact absurd hbox.1.2 (not_le.2 h)
    · exact absurd hbox.2.1 (not_le.2 h)
    · exact absurd hbox.2.2 (not_le.2 h)

/-- a ray leaves every bounded set -/
theorem ray_leaves {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B) (x : ℝ × ℝ) {d : ℝ × ℝ}
    (hd : d ≠ 0) : ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ s, S₀ ≤ s → x + s • d ∉ B := by
  obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : ℝ × ℝ)
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  refine ⟨(|R| + ‖x‖ + 1) / ‖d‖, by positivity, fun s hs hmem => ?_⟩
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : (|R| + ‖x‖ + 1) ≤ s * ‖d‖ := (div_le_iff₀ hdn).1 hs
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have h3 : ‖s • d‖ = s * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have h4 : ‖s • d‖ ≤ ‖x + s • d‖ + ‖x‖ := by
    have := norm_sub_le (x + s • d) x
    rwa [add_sub_cancel_left] at this
  linarith [le_abs_self R]

/-! ### The two sides of the curve -/

/-- a point from which a segment free of the curve leads to a point of a side (not an end point)
is joined to the left or to the right side of this side -/
private theorem side_of_hit (hs : Simple v σ) {x d : ℝ × ℝ} {s₀ : ℝ} (hpos : 0 < s₀)
    (hfree : ∀ s ∈ Ico 0 s₀, x + s • d ∉ curveCyc v σ) {k : ι} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hhit : x + s₀ • d = pt (v k) (v (σ k)) t) :
    SideOf v σ 1 k t x ∨ SideOf v σ (-1) k t x := by
  have hx0 : x + (0 : ℝ) • d = x := by rw [zero_smul, add_zero]
  have hpre : IsPreconnected ((fun s : ℝ => x + s • d) '' Ico 0 s₀) :=
    isPreconnected_Ico.image _ (continuous_ray x d).continuousOn
  have hsub : (fun s : ℝ => x + s • d) '' Ico 0 s₀ ⊆ (curveCyc v σ)ᶜ := by
    rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
  have hjoin : ∀ s ∈ Ico 0 s₀, Joined v σ (x + s • d) x := fun s hs' =>
    Joined.of_mem hpre hsub ⟨s, hs', rfl⟩ ⟨0, ⟨le_rfl, hpos⟩, hx0⟩
  have hmem : ∀ᶠ s in 𝓝[<] s₀, s ∈ Ioo 0 s₀ := Ioo_mem_nhdsLT hpos
  have hb : ∀ e : ℝ, ∀ᶠ s in 𝓝[<] s₀, 0 < e * cross (v k) (v (σ k)) (x + s • d) →
      SideOf v σ e k t (x + s • d) := by
    intro e
    have := half_ball hs k ht e
    rw [← hhit] at this
    exact ((continuous_ray x d).continuousAt.eventually this).filter_mono nhdsWithin_le_nhds
  have hn : ∀ᶠ s in 𝓝[<] s₀, cross (v k) (v (σ k)) (x + s • d) = 0 →
      x + s • d ∈ segment ℝ (v k) (v (σ k)) := by
    have := near_side (hs.ne k) ht
    rw [← hhit] at this
    exact ((continuous_ray x d).continuousAt.eventually this).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, h1, h2, h3, h4⟩ := (hmem.and ((hb 1).and ((hb (-1)).and hn))).exists
  have hsI : s ∈ Ico 0 s₀ := ⟨h1.1.le, h1.2⟩
  have hne : cross (v k) (v (σ k)) (x + s • d) ≠ 0 :=
    fun h0 => hfree s hsI (mem_iUnion.2 ⟨k, h4 h0⟩)
  rcases lt_or_gt_of_ne hne with h | h
  · right; exact (h3 (by linarith)).of_joined (hjoin s hsI)
  · left; exact (h2 (by linarith)).of_joined (hjoin s hsI)

/-- **The two sides of a simple closed polygon.**  There are two points `xL` (winding number
`l`) and `xR` (winding number `l - 1`) off the curve such that every point off the curve can be
joined to `xL` or to `xR` by a connected set which does not meet the curve. -/
theorem two_sides (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l) :
    ∃ xL xR, xL ∉ curveCyc v σ ∧ xR ∉ curveCyc v σ ∧ wind v σ xL = l ∧ wind v σ xR = l - 1 ∧
      ∀ x, x ∉ curveCyc v σ → Joined v σ x xL ∨ Joined v σ x xR := by
  obtain ⟨xL, hLc, hLw, hL⟩ := SideOf.all hs hl (e := 1) one_ne_zero
  obtain ⟨xR, hRc, hRw, hR⟩ := SideOf.all hs hl (e := -1) (by norm_num)
  have hLw' : wind v σ xL = l := by rw [hLw, sideWind, ite_eq_left one_pos]
  have hRw' : wind v σ xR = l - 1 := by rw [hRw, sideWind, ite_eq_right (by norm_num)]
  refine ⟨xL, xR, hLc, hRc, hLw', hRw', ?_⟩
  have key : ∀ x k t, t ∈ Ioo (0 : ℝ) 1 → (SideOf v σ 1 k t x ∨ SideOf v σ (-1) k t x) →
      Joined v σ x xL ∨ Joined v σ x xR := by
    intro x k t ht h
    rcases h with h | h
    · left; exact h.join hs one_ne_zero (hL k t ht)
    · right; exact h.join hs (by norm_num) (hR k t ht)
  obtain ⟨F, hF, hFb, hFr⟩ := exists_far_set v σ
  have hFU : F ⊆ (curveCyc v σ)ᶜ := fun y hy hc => hFr hy (Or.inl hc)
  have hfar : ∀ (x d : ℝ × ℝ), d ≠ 0 → ∃ S₀ : ℝ, 0 ≤ S₀ ∧ x + S₀ • d ∈ F := by
    intro x d hd
    obtain ⟨S₀, h0, h⟩ := ray_leaves hFb x hd
    exact ⟨S₀, h0, not_not.1 (h S₀ le_rfl)⟩
  -- a far point which is joined to `xL` or `xR`
  obtain ⟨i₀, -⟩ := hs.cyc
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hq : pt (v i₀) (v (σ i₀)) (1 / 2) ∈ curveCyc v σ :=
    mem_iUnion.2 ⟨i₀, pt_mem_segment _ _ hhalf.1.le hhalf.2.le⟩
  obtain ⟨d, hd0, hd⟩ := exists_generic_dir v (hs.pt_ne_vertex i₀ hhalf.1 hhalf.2)
  obtain ⟨S, hS0, hSF⟩ := hfar (pt (v i₀) (v (σ i₀)) (1 / 2)) (-d) (neg_ne_zero.2 hd0)
  have hline : ∀ s : ℝ, pt (v i₀) (v (σ i₀)) (1 / 2) + S • (-d) + s • d =
      pt (v i₀) (v (σ i₀)) (1 / 2) + (s - S) • d := fun s => by module
  have hy : Joined v σ (pt (v i₀) (v (σ i₀)) (1 / 2) + S • (-d)) xL ∨
      Joined v σ (pt (v i₀) (v (σ i₀)) (1 / 2) + S • (-d)) xR := by
    rcases ray_first_hit hs (hFU hSF) (d := d) (fun i s _ => by rw [hline]; exact hd i _) with
      hfree | ⟨s₀, hpos, hfree, k, t, ht, hhit⟩
    · exfalso
      apply hfree S hS0
      rw [hline, sub_self, zero_smul, add_zero]
      exact hq
    · exact key _ k t ht (side_of_hit hs hpos hfree ht hhit)
  intro x hx
  have hxv : ∀ i, x ≠ v i :=
    fun i h => notMem_curveCyc.1 hx i (h ▸ left_mem_segment ℝ _ _)
  obtain ⟨d', hd0', hd'⟩ := exists_generic_dir v hxv
  rcases ray_first_hit hs hx (fun i s _ => hd' i s) with hfree | ⟨s₀, hpos, hfree, k, t, ht, hhit⟩
  · obtain ⟨S', hS0', hSF'⟩ := hfar x d' hd0'
    have hpre : IsPreconnected ((fun s : ℝ => x + s • d') '' Ici 0) :=
      isPreconnected_Ici.image _ (continuous_ray x d').continuousOn
    have hsub : (fun s : ℝ => x + s • d') '' Ici 0 ⊆ (curveCyc v σ)ᶜ := by
      rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
    have h1 : Joined v σ x (x + S' • d') :=
      Joined.of_mem hpre hsub
        ⟨0, mem_Ici.2 le_rfl, by show x + (0 : ℝ) • d' = x; rw [zero_smul, add_zero]⟩
        ⟨S', hS0', rfl⟩
    have h2 := h1.trans (Joined.of_mem hF hFU hSF' hSF)
    rcases hy with h | h
    · left; exact h2.trans h
    · right; exact h2.trans h
  · exact key x k t ht (side_of_hit hs hpos hfree ht hhit)

/-- **the points off the curve with a given winding number form a connected set** -/
theorem isPreconnected_wind_eq (hs : Simple v σ) (n : ℤ) :
    IsPreconnected {x | x ∉ curveCyc v σ ∧ wind v σ x = n} := by
  obtain ⟨l, hl⟩ := wind_side_all hs
  obtain ⟨xL, xR, hLc, hRc, hLw, hRw, hall⟩ := two_sides hs hl
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hj : Joined v σ x y := by
    rcases hall x hx.1 with h1 | h1 <;> rcases hall y hy.1 with h2 | h2
    · exact h1.trans h2.symm
    · exfalso
      have e1 := h1.wind_eq
      have e2 := h2.wind_eq
      rw [hx.2, hLw] at e1
      rw [hy.2, hRw] at e2
      omega
    · exfalso
      have e1 := h1.wind_eq
      have e2 := h2.wind_eq
      rw [hx.2, hRw] at e1
      rw [hy.2, hLw] at e2
      omega
    · exact h1.trans h2.symm
  obtain ⟨S, hS, hSU, hxS, hyS⟩ := hj
  exact ⟨S, fun z hz => ⟨hSU hz, (wind_const_on hS hSU hz hxS).trans hx.2⟩, hxS, hyS, hS⟩

/-- both winding numbers `l` and `l - 1` occur off the curve -/
theorem exists_wind_eq (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l) :
    (∃ x, x ∉ curveCyc v σ ∧ wind v σ x = l) ∧ (∃ x, x ∉ curveCyc v σ ∧ wind v σ x = l - 1) := by
  obtain ⟨xL, xR, hLc, hRc, hLw, hRw, -⟩ := two_sides hs hl
  exact ⟨⟨xL, hLc, hLw⟩, ⟨xR, hRc, hRw⟩⟩

end

end Stein.Polygon
