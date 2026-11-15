import Stein.Polygon.Frontier

/-!
# Rays from a point off a simple closed polygon

Let `v`, `σ` be a simple closed polygon (`Stein.Polygon.Simple`) and `x` a point off the curve.

* `wind_const_on` : the winding number is constant on connected sets which do not meet the curve.
* `exists_far` : every ray leaves the region `regionCyc v σ`.
* `exists_generic_dir` : there is a direction `d` such that the line through `x` in the direction
  `d` contains no vertex.
* `ray_first_hit` : a ray from `x` which contains no vertex either does not meet the curve, or its
  first point on the curve is a point of a side, not an end point.
* `ray_jump`, `ray_parallel` : the winding number along a line through a point of a side.
* `wind_mem_pair` : off the curve, the winding number takes only the two values `l` and `l - 1`,
  where `l` (`= 1` or `0`) is its value on the sides.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

/-! ### Lines and rays -/

/-- near a point of the open segment `a b`, the points of the line `a b` are on the segment -/
theorem near_side {a b : ℝ × ℝ} (hab : a ≠ b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 (pt a b t), cross a b y = 0 → y ∈ segment ℝ a b := by
  have hd := sqdist_pos hab
  set τ : ℝ × ℝ → ℝ := fun y => ((y.1 - a.1) * (b.1 - a.1) + (y.2 - a.2) * (b.2 - a.2)) /
    ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) with hτ
  have hc : Continuous τ := by fun_prop
  have h0 : τ (pt a b t) = t := by
    simp only [hτ, pt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    field_simp
    ring
  have hev : ∀ᶠ y in 𝓝 (pt a b t), τ y ∈ Ioo (0 : ℝ) 1 :=
    hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact Ioo_mem_nhds ht.1 ht.2)
  filter_upwards [hev] with y hy hcr
  rw [segment_eq_pt]
  refine ⟨τ y, ⟨hy.1.le, hy.2.le⟩, ?_⟩
  have hτy : τ y * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) =
      (y.1 - a.1) * (b.1 - a.1) + (y.2 - a.2) * (b.2 - a.2) := div_mul_cancel₀ _ hd.ne'
  unfold cross at hcr
  apply Prod.ext
  · apply mul_right_cancel₀ hd.ne'
    simp only [pt, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    linear_combination (b.1 - a.1) * hτy + (b.2 - a.2) * hcr
  · apply mul_right_cancel₀ hd.ne'
    simp only [pt, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    linear_combination (b.2 - a.2) * hτy - (b.1 - a.1) * hcr

/-- `cross` along a line `s ↦ x + s • d` -/
theorem cross_ray (a b x d : ℝ × ℝ) (s s₀ : ℝ) :
    cross a b (x + s • d) = cross a b (x + s₀ • d) +
      ((b.1 - a.1) * d.2 - (b.2 - a.2) * d.1) * (s - s₀) := by
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- the parametrisation `s ↦ x + s • d` of a line is continuous -/
theorem continuous_ray (x d : ℝ × ℝ) : Continuous (fun s : ℝ => x + s • d) := by fun_prop

/-! ### The winding number along a ray -/

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

omit [Fintype ι] in
/-- a point is off the curve iff it is on no side -/
theorem notMem_curveCyc {x : ℝ × ℝ} :
    x ∉ curveCyc v σ ↔ ∀ i, x ∉ segment ℝ (v i) (v (σ i)) := by
  simp [curveCyc]

/-- a closed polygonal curve is a closed set -/
theorem isClosed_curveCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : IsClosed (curveCyc v σ) :=
  isClosed_iUnion_of_finite (fun _ => isClosed_segment' _ _)

/-- **the winding number is constant on connected sets which do not meet the curve** -/
theorem wind_const_on {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hSU : S ⊆ (curveCyc v σ)ᶜ)
    {x y : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) : wind v σ x = wind v σ y := by
  have hcont : ContinuousOn (wind v σ) S := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.congr
      (EventuallyEq.symm (wind_eventually_eq v σ (notMem_curveCyc.1 (hSU hz))))
  exact hS.constant hcont hx hy

/-- a ray leaves the (bounded) region -/
theorem exists_far (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (x : ℝ × ℝ) {d : ℝ × ℝ} (hd : d ≠ 0) :
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ s, S₀ ≤ s → x + s • d ∉ regionCyc v σ := by
  obtain ⟨R, hR⟩ := (isCompact_regionCyc v σ).isBounded.subset_closedBall (0 : ℝ × ℝ)
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

/-- outside the region the winding number vanishes -/
theorem wind_eq_zero_of_notMem_region {x : ℝ × ℝ} (hx : x ∉ regionCyc v σ) : wind v σ x = 0 := by
  by_contra h
  exact hx (Or.inr h)

/-- the first point of a ray on the curve: if the ray from `x` (not on the curve) contains no
vertex, either it does not meet the curve, or its first point on the curve is a point of a side,
not an end point -/
theorem ray_first_hit (_hs : Simple v σ) {x d : ℝ × ℝ} (hx : x ∉ curveCyc v σ)
    (hd : ∀ i, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v i) :
    (∀ s : ℝ, 0 ≤ s → x + s • d ∉ curveCyc v σ) ∨
    ∃ s₀ : ℝ, 0 < s₀ ∧ (∀ s ∈ Ico 0 s₀, x + s • d ∉ curveCyc v σ) ∧
      ∃ k, ∃ t ∈ Ioo (0 : ℝ) 1, x + s₀ • d = pt (v k) (v (σ k)) t := by
  set T : Set ℝ := {s | 0 ≤ s ∧ x + s • d ∈ curveCyc v σ} with hT
  by_cases hne : T.Nonempty
  · right
    have hcl : IsClosed T :=
      isClosed_Ici.inter ((isClosed_curveCyc v σ).preimage (continuous_ray x d))
    have hbdd : BddBelow T := ⟨0, fun s hs => hs.1⟩
    have hmem := hcl.csInf_mem hne hbdd
    set s₀ := sInf T with hs₀
    have hpos : 0 < s₀ := by
      rcases hmem.1.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hx
        have := hmem.2
        rwa [← h, zero_smul, add_zero] at this
    refine ⟨s₀, hpos, fun s hs hc => ?_, ?_⟩
    · exact absurd (csInf_le hbdd (show s ∈ T from ⟨hs.1, hc⟩)) (not_le.2 hs.2)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hmem.2
      obtain ⟨t, ht, e⟩ := mem_segment_pt hk (hd k s₀ hpos.le) (hd (σ k) s₀ hpos.le)
      exact ⟨k, t, ht, e.symm⟩
  · left
    intro s hs hc
    exact hne ⟨s, hs, hc⟩

/-- the winding number along a line through a point `x + s₀ • d` of a side, the line being
transversal to the side -/
theorem ray_jump (hs : Simple v σ) (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {x d : ℝ × ℝ} {s₀ : ℝ}
    (hx : x + s₀ • d = pt (v k) (v (σ k)) t) :
    ∀ᶠ s in 𝓝 s₀,
      (0 < (((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1) * (s - s₀) →
        wind v σ (x + s • d) = wind v σ (pt (v k) (v (σ k)) t)) ∧
      ((((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1) * (s - s₀) < 0 →
        wind v σ (x + s • d) = wind v σ (pt (v k) (v (σ k)) t) - 1) := by
  have hj := wind_jump v σ k (hs.ne k) ht.1 ht.2 (hs.pt_not_mem k ht.1 ht.2)
  rw [← hx] at hj
  have hj' := (continuous_ray x d).continuousAt.eventually hj
  filter_upwards [hj'] with s h
  have hc := cross_ray (v k) (v (σ k)) x d s s₀
  rw [hx, cross_of_mem_segment (pt_mem_segment _ _ ht.1.le ht.2.le), zero_add] at hc
  rw [← hc, ← hx]
  exact h

omit [Fintype ι] in
/-- a line through a point of a side, not an end point, and parallel to the side stays in the side
near this point -/
theorem ray_parallel (k : ι) (hab : v k ≠ v (σ k)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {x d : ℝ × ℝ} {s₀ : ℝ} (hx : x + s₀ • d = pt (v k) (v (σ k)) t)
    (hc : ((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1 = 0) :
    ∀ᶠ s in 𝓝 s₀, x + s • d ∈ segment ℝ (v k) (v (σ k)) := by
  have hn := near_side hab ht
  rw [← hx] at hn
  filter_upwards [(continuous_ray x d).continuousAt.eventually hn] with s h
  apply h
  rw [cross_ray (v k) (v (σ k)) x d s s₀, hc, zero_mul, add_zero, hx]
  exact cross_of_mem_segment (pt_mem_segment _ _ ht.1.le ht.2.le)

omit [Fintype ι] in
/-- there is a direction `d` such that the line through `x` in the direction `d` contains no
vertex -/
theorem exists_generic_dir [Finite ι] (v : ι → ℝ × ℝ) {x : ℝ × ℝ} (hx : ∀ i, x ≠ v i) :
    ∃ d : ℝ × ℝ, d ≠ 0 ∧ ∀ i, ∀ s : ℝ, x + s • d ≠ v i := by
  by_contra hcon
  have h : ∀ n : ℕ, ∃ i, ∃ s : ℝ, x + s • ((1 : ℝ), (n : ℝ)) = v i := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨(1, n), ?_, fun i s h => hn ⟨i, s, h⟩⟩
    intro h0
    have := congrArg Prod.fst h0
    simp at this
  choose f s hfs using h
  obtain ⟨n, m, hnm, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have e1 := hfs n
  have e2 := hfs m
  rw [hf] at e1
  have h1 : x.1 + s n = (v (f m)).1 := by
    have := congrArg Prod.fst e1; simpa using this
  have h2 : x.2 + s n * n = (v (f m)).2 := by
    have := congrArg Prod.snd e1; simpa using this
  have h3 : x.1 + s m = (v (f m)).1 := by
    have := congrArg Prod.fst e2; simpa using this
  have h4 : x.2 + s m * m = (v (f m)).2 := by
    have := congrArg Prod.snd e2; simpa using this
  have hsm : s n = s m := by linarith
  have h5 : s m * ((n : ℝ) - m) = 0 := by rw [hsm] at h2; linarith
  have hnm' : (n : ℝ) - m ≠ 0 := by
    intro h; apply hnm; exact_mod_cast sub_eq_zero.1 h
  have h6 : s m = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact h
    · exact absurd h hnm'
  apply hx (f m)
  apply Prod.ext
  · rw [← h3, h6, add_zero]
  · rw [← h4, h6, zero_mul, add_zero]

/-- **Off the curve, the winding number of a simple closed polygon takes only the two values
`l` and `l - 1`**, where `l` (`= 1` or `0`) is its value on the sides. -/
theorem wind_mem_pair (hs : Simple v σ) {l : ℤ} (hl01 : l = 1 ∨ l = 0)
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    {x : ℝ × ℝ} (hx : x ∉ curveCyc v σ) : wind v σ x = l ∨ wind v σ x = l - 1 := by
  have hxv : ∀ i, x ≠ v i :=
    fun i h => notMem_curveCyc.1 hx i (h ▸ left_mem_segment ℝ _ _)
  obtain ⟨d, hd0, hd⟩ := exists_generic_dir v hxv
  have hx0 : x + (0 : ℝ) • d = x := by rw [zero_smul, add_zero]
  rcases ray_first_hit hs hx (fun i s _ => hd i s) with hfree | ⟨s₀, hpos, hfree, k, t, ht, hhit⟩
  · obtain ⟨S₀, hS0, hS⟩ := exists_far v σ x hd0
    have hpre : IsPreconnected ((fun s : ℝ => x + s • d) '' Ici 0) :=
      isPreconnected_Ici.image _ (continuous_ray x d).continuousOn
    have hsub : (fun s : ℝ => x + s • d) '' Ici 0 ⊆ (curveCyc v σ)ᶜ := by
      rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
    have := wind_const_on hpre hsub ⟨0, mem_Ici.2 le_rfl, hx0⟩ ⟨S₀, hS0, rfl⟩
    rw [this, wind_eq_zero_of_notMem_region (hS S₀ le_rfl)]
    rcases hl01 with h | h
    · right; rw [h]; norm_num
    · left; rw [h]
  · have hpre : IsPreconnected ((fun s : ℝ => x + s • d) '' Ico 0 s₀) :=
      isPreconnected_Ico.image _ (continuous_ray x d).continuousOn
    have hsub : (fun s : ℝ => x + s • d) '' Ico 0 s₀ ⊆ (curveCyc v σ)ᶜ := by
      rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
    have hconst : ∀ s ∈ Ico 0 s₀, wind v σ x = wind v σ (x + s • d) := fun s hs' =>
      wind_const_on hpre hsub ⟨0, ⟨le_rfl, hpos⟩, hx0⟩ ⟨s, hs', rfl⟩
    have hmem : ∀ᶠ s in 𝓝[<] s₀, s ∈ Ioo 0 s₀ := Ioo_mem_nhdsLT hpos
    by_cases hc : ((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1 = 0
    · exfalso
      have hp := (ray_parallel k (hs.ne k) ht hhit hc).filter_mono
        (nhdsWithin_le_nhds (s := Iio s₀))
      obtain ⟨s, h1, h2⟩ := (hmem.and hp).exists
      exact hfree s ⟨h1.1.le, h1.2⟩ (mem_iUnion.2 ⟨k, h2⟩)
    · have hj := (ray_jump hs k ht hhit).filter_mono (nhdsWithin_le_nhds (s := Iio s₀))
      obtain ⟨s, h1, h2⟩ := (hmem.and hj).exists
      rw [hconst s ⟨h1.1.le, h1.2⟩]
      rw [hl k t ht] at h2
      have hne : (((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1) * (s - s₀) ≠ 0 :=
        mul_ne_zero hc (sub_ne_zero.2 h1.2.ne)
      rcases lt_or_gt_of_ne hne with h | h
      · right; exact h2.2 h
      · left; exact h2.1 h

end cyc

end

end Stein.Polygon
