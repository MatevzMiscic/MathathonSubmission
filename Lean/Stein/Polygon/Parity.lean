import Stein.Polygon.Jordan

/-!
# Ray-crossing parity for simple closed polygons

For a simple closed polygon `v`, a point `x` off the curve and a ray `s ↦ x + s • d` (`s ≥ 0`,
`d ≠ 0`) which contains no vertex, `x` belongs to `region v` iff the number of sides met by the
ray is odd (`mem_region_iff_odd_crossings`).  Such rays exist (`exists_generic_ray`); a ray
without vertices meets every side in at most one point (`ray_side_subsingleton`), so the number
of sides met is the number of crossing points (`ray_side_unique`).

These statements are not used in the proof of the main theorem; they show that `region v`
(`Stein/Polygon/Region.lean`) is the region bounded by the polygon `v` in the sense of the
even-odd rule.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- **ray-crossing parity**, abstract version, by induction on the number of sides met -/
theorem ray_parity (hs : Simple v σ) {d : ℝ × ℝ} (hd0 : d ≠ 0) :
    ∀ n : ℕ, ∀ x : ℝ × ℝ, x ∉ curveCyc v σ → (∀ i, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v i) →
      {k | ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ segment ℝ (v k) (v (σ k))}.ncard = n →
      (wind v σ x ≠ 0 ↔ Odd n) := by
  obtain ⟨l, hl01, hl⟩ : ∃ l : ℤ, (l = 1 ∨ l = 0) ∧
      ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l := by
    rcases wind_side_cases hs with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨0, Or.inr rfl, h⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx hd hn
  have hx0 : x + (0 : ℝ) • d = x := by rw [zero_smul, add_zero]
  rcases ray_first_hit hs hx hd with hfree | ⟨s₀, hpos, hfree, k, t, ht, hhit⟩
  · have hempty : {k | ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ segment ℝ (v k) (v (σ k))} = ∅ := by
      ext k
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨s, hs0, hmem⟩
      exact hfree s hs0 (mem_iUnion.2 ⟨k, hmem⟩)
    rw [hempty, ncard_empty] at hn
    obtain ⟨S₀, hS0, hS⟩ := exists_far v σ x hd0
    have hpre : IsPreconnected ((fun s : ℝ => x + s • d) '' Ici 0) :=
      isPreconnected_Ici.image _ (continuous_ray x d).continuousOn
    have hsub : (fun s : ℝ => x + s • d) '' Ici 0 ⊆ (curveCyc v σ)ᶜ := by
      rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
    have hw := wind_const_on hpre hsub ⟨0, mem_Ici.2 le_rfl, hx0⟩ ⟨S₀, hS0, rfl⟩
    rw [wind_eq_zero_of_notMem_region (hS S₀ le_rfl)] at hw
    rw [← hn, hw]
    simp
  · set c : ℝ := ((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1 with hc
    have hcross : ∀ s, cross (v k) (v (σ k)) (x + s • d) = c * (s - s₀) := by
      intro s
      rw [cross_ray (v k) (v (σ k)) x d s s₀, hhit, cross_pt, zero_add]
    have hc0 : c ≠ 0 := by
      intro h0
      have hp := (ray_parallel k (hs.ne k) ht hhit h0).filter_mono
        (nhdsWithin_le_nhds (s := Iio s₀))
      have hmem : ∀ᶠ s in 𝓝[<] s₀, s ∈ Ioo 0 s₀ := Ioo_mem_nhdsLT hpos
      obtain ⟨s, h1, h2⟩ := (hmem.and hp).exists
      exact hfree s ⟨h1.1.le, h1.2⟩ (mem_iUnion.2 ⟨k, h2⟩)
    have hoth : ∀ᶠ s in 𝓝 s₀, ∀ j, j ≠ k → x + s • d ∉ segment ℝ (v j) (v (σ j)) := by
      have := eventually_off_others hs k ht
      rw [← hhit] at this
      exact (continuous_ray x d).continuousAt.eventually this
    obtain ⟨a, b, hab, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 ((ray_jump hs k ht hhit).and hoth)
    have hoff : ∀ s ∈ Ioo a b, s ≠ s₀ → x + s • d ∉ curveCyc v σ := by
      intro s hs' hne hmem
      obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
      by_cases hjk : j = k
      · rw [hjk] at hj
        have := cross_of_mem_segment hj
        rw [hcross] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hc0 h
        · exact hne (sub_eq_zero.1 h)
      · exact (hsub hs').2 j hjk hj
    have hm : max a 0 < s₀ := max_lt hab.1 hpos
    obtain ⟨s₁, hs1⟩ : ∃ s₁, s₁ = (s₀ + b) / 2 := ⟨_, rfl⟩
    obtain ⟨s₂, hs2⟩ : ∃ s₂, s₂ = (max a 0 + s₀) / 2 := ⟨_, rfl⟩
    have h1 : s₀ < s₁ ∧ s₁ < b := by
      have := hab.2
      constructor <;> rw [hs1] <;> linarith
    have h2 : max a 0 < s₂ ∧ s₂ < s₀ := by constructor <;> rw [hs2] <;> linarith
    have hs1I : s₁ ∈ Ioo a b := ⟨by linarith [hab.1], h1.2⟩
    have hs2I : s₂ ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) h2.1, by linarith [hab.2]⟩
    have hs2pos : 0 ≤ s₂ := (le_max_right a 0).trans h2.1.le
    have hwx : wind v σ x = wind v σ (x + s₂ • d) := by
      have hpre : IsPreconnected ((fun s : ℝ => x + s • d) '' Ico 0 s₀) :=
        isPreconnected_Ico.image _ (continuous_ray x d).continuousOn
      have hsub' : (fun s : ℝ => x + s • d) '' Ico 0 s₀ ⊆ (curveCyc v σ)ᶜ := by
        rintro _ ⟨s, hs', rfl⟩; exact hfree s hs'
      exact wind_const_on hpre hsub' ⟨0, ⟨le_rfl, hpos⟩, hx0⟩ ⟨s₂, ⟨hs2pos, h2.2⟩, rfl⟩
    have hw12 : (wind v σ (x + s₁ • d) = l ∧ wind v σ (x + s₂ • d) = l - 1) ∨
        (wind v σ (x + s₁ • d) = l - 1 ∧ wind v σ (x + s₂ • d) = l) := by
      have j1 := (hsub hs1I).1
      have j2 := (hsub hs2I).1
      rw [hl k t ht] at j1 j2
      rcases lt_or_gt_of_ne hc0 with h | h
      · right
        exact ⟨j1.2 (mul_neg_of_neg_of_pos h (sub_pos.2 h1.1)),
          j2.1 (mul_pos_of_neg_of_neg h (sub_neg.2 h2.2))⟩
      · left
        exact ⟨j1.1 (mul_pos h (sub_pos.2 h1.1)),
          j2.2 (mul_neg_of_pos_of_neg h (sub_neg.2 h2.2))⟩
    have hx' : x + s₁ • d ∉ curveCyc v σ := hoff s₁ hs1I h1.1.ne'
    have hray : ∀ s : ℝ, x + s₁ • d + s • d = x + (s₁ + s) • d := fun s => by module
    have hd' : ∀ i, ∀ s : ℝ, 0 ≤ s → x + s₁ • d + s • d ≠ v i := fun i s hs0 => by
      rw [hray]; exact hd i _ (by linarith)
    have hH : {j | ∃ s : ℝ, 0 ≤ s ∧ x + s₁ • d + s • d ∈ segment ℝ (v j) (v (σ j))} =
        {j | ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ segment ℝ (v j) (v (σ j))} \ {k} := by
      ext j
      simp only [mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨s, hs0, hmem⟩
        rw [hray] at hmem
        refine ⟨⟨s₁ + s, by linarith, hmem⟩, ?_⟩
        intro hjk
        rw [hjk] at hmem
        have := cross_of_mem_segment hmem
        rw [hcross] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hc0 h
        · linarith
      · rintro ⟨⟨s, hs0, hmem⟩, hjk⟩
        have hge : s₁ ≤ s := by
          by_contra hlt
          rw [not_le] at hlt
          have hcurve : x + s • d ∈ curveCyc v σ := mem_iUnion.2 ⟨j, hmem⟩
          rcases lt_trichotomy s s₀ with h | h | h
          · exact hfree s ⟨hs0, h⟩ hcurve
          · rw [h, hhit] at hmem
            exact hs.pt_not_mem k ht.1 ht.2 j hjk hmem
          · exact hoff s ⟨by linarith [hab.1], by linarith⟩ h.ne' hcurve
        refine ⟨s - s₁, by linarith, ?_⟩
        rw [hray, add_sub_cancel]
        exact hmem
    have hk : k ∈ {j | ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ segment ℝ (v j) (v (σ j))} :=
      ⟨s₀, hpos.le, by rw [hhit]; exact pt_mem_segment _ _ ht.1.le ht.2.le⟩
    have hnpos : 0 < n := by rw [← hn]; exact (ncard_pos).2 ⟨k, hk⟩
    have hcard : {j | ∃ s : ℝ, 0 ≤ s ∧ x + s₁ • d + s • d ∈ segment ℝ (v j) (v (σ j))}.ncard =
        n - 1 := by
      rw [hH, ncard_sdiff_singleton_of_mem hk, hn]
    have hih := ih (n - 1) (by omega) (x + s₁ • d) hx' hd' hcard
    have hpar : Odd n ↔ ¬ Odd (n - 1) := by
      rw [Nat.odd_iff, Nat.odd_iff]; omega
    rw [hwx, hpar, ← hih]
    rcases hw12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hl01 with rfl | rfl <;> rw [e1, e2] <;>
      norm_num

/-- a ray from a point off the curve which contains no vertex meets every side in at most one
point -/
theorem ray_side_subsingleton (hs : Simple v σ) {x d : ℝ × ℝ} (hx : x ∉ curveCyc v σ)
    (hd : ∀ i, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v i) (k : ι) {s s' : ℝ} (hs0 : 0 ≤ s) (_hs0' : 0 ≤ s')
    (h : x + s • d ∈ segment ℝ (v k) (v (σ k))) (h' : x + s' • d ∈ segment ℝ (v k) (v (σ k))) :
    s = s' := by
  by_contra hne
  have hc := cross_of_mem_segment h
  have hc' := cross_of_mem_segment h'
  rw [cross_ray (v k) (v (σ k)) x d s s', hc', zero_add] at hc
  have hc0 : ((v (σ k)).1 - (v k).1) * d.2 - ((v (σ k)).2 - (v k).2) * d.1 = 0 := by
    rcases mul_eq_zero.1 hc with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0) hne
  -- the whole ray is on the line of the side; it starts off the side and reaches it
  have hline : ∀ r : ℝ, cross (v k) (v (σ k)) (x + r • d) = 0 := by
    intro r
    rw [cross_ray (v k) (v (σ k)) x d r s', hc', hc0, zero_mul, add_zero]
  have hx0 : x + (0 : ℝ) • d = x := by rw [zero_smul, add_zero]
  rcases ray_first_hit hs hx hd with hfree | ⟨s₀, hpos, hfree, j, t, ht, hhit⟩
  · exact hfree s hs0 (mem_iUnion.2 ⟨k, h⟩)
  · by_cases hjk : j = k
    · rw [hjk] at hhit
      have hp := (ray_parallel k (hs.ne k) ht hhit hc0).filter_mono
        (nhdsWithin_le_nhds (s := Iio s₀))
      have hmem : ∀ᶠ s in 𝓝[<] s₀, s ∈ Ioo 0 s₀ := Ioo_mem_nhdsLT hpos
      obtain ⟨r, h1, h2⟩ := (hmem.and hp).exists
      exact hfree r ⟨h1.1.le, h1.2⟩ (mem_iUnion.2 ⟨k, h2⟩)
    · -- the first hit is on another side `j`; the ray crosses it and stays on the line of `k`
      -- the hit point is on the line of the side `k` and not on the side `k`
      have hnk : x + s₀ • d ∉ segment ℝ (v k) (v (σ k)) := by
        rw [hhit]; exact hs.pt_not_mem j ht.1 ht.2 k (Ne.symm hjk)
      -- the set of parameters of the ray on the side `k` is an interval not containing `s₀`,
      -- nor any parameter before `s₀`; both `s` and `s'` are beyond `s₀`
      have hbig : ∀ r : ℝ, 0 ≤ r → x + r • d ∈ segment ℝ (v k) (v (σ k)) → s₀ < r := by
        intro r hr0 hr
        by_contra hle
        rcases (not_lt.1 hle).lt_or_eq with h1 | h1
        · exact hfree r ⟨hr0, h1⟩ (mem_iUnion.2 ⟨k, hr⟩)
        · rw [h1] at hr; exact hnk hr
      -- the point at `s₀` lies between `x` and the point at `s`, all on the line of `k`:
      -- the segment `k` is convex, hence a point of the line beyond... we use the vertices
      have hd0 : d ≠ 0 := by
        intro h0
        apply hx
        have := h
        rw [h0, smul_zero, add_zero] at this
        exact mem_iUnion.2 ⟨k, this⟩
      -- parametrise the line of the side `k` by the ray: both end points are on the ray line
      have hab := hs.ne k
      have hpar : ∀ p : ℝ × ℝ, cross (v k) (v (σ k)) p = 0 → ∃ r : ℝ, p = x + r • d := by
        intro p hp
        have hD := sqdist_pos (show (0 : ℝ × ℝ) ≠ d from fun h => hd0 h.symm)
        simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hD
        have hpx := hline 0
        rw [hx0] at hpx
        unfold cross at hp hpx
        refine ⟨((p.1 - x.1) * d.1 + (p.2 - x.2) * d.2) / (d.1 ^ 2 + d.2 ^ 2), ?_⟩
        have hab' := sqdist_pos hab
        have key : (p.1 - x.1) * d.2 - (p.2 - x.2) * d.1 = 0 := by
          have e1 : ((v (σ k)).1 - (v k).1) * ((p.1 - x.1) * d.2 - (p.2 - x.2) * d.1) = 0 := by
            linear_combination (-d.1) * hp + d.1 * hpx + (p.1 - x.1) * hc0
          have e2 : ((v (σ k)).2 - (v k).2) * ((p.1 - x.1) * d.2 - (p.2 - x.2) * d.1) = 0 := by
            linear_combination (-d.2) * hp + d.2 * hpx + (p.2 - x.2) * hc0
          by_contra hne'
          have z1 := (mul_eq_zero.1 e1).resolve_right hne'
          have z2 := (mul_eq_zero.1 e2).resolve_right hne'
          rw [z1, z2] at hab'
          norm_num at hab'
        apply Prod.ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          field_simp
          linear_combination d.2 * key
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          field_simp
          linear_combination (-d.1) * key
      obtain ⟨ra, hra⟩ := hpar (v k) (cross_of_mem_segment (left_mem_segment ℝ _ _))
      obtain ⟨rb, hrb⟩ := hpar (v (σ k)) (cross_of_mem_segment (right_mem_segment ℝ _ _))
      have hra0 : ra < 0 := by
        by_contra hge
        exact hd k ra (not_lt.1 hge) hra.symm
      have hrb0 : rb < 0 := by
        by_contra hge
        exact hd (σ k) rb (not_lt.1 hge) hrb.symm
      -- a point of the segment has a parameter between `ra` and `rb`, hence negative
      rw [segment_eq_pt] at h
      obtain ⟨τ, hτ, e⟩ := h
      have e' : x + s • d = x + ((1 - τ) * ra + τ * rb) • d := by
        rw [← e, pt]
        conv_lhs => rw [hra, hrb]
        module
      have e'' : (s - ((1 - τ) * ra + τ * rb)) • d = 0 := by
        have := sub_eq_zero.2 e'
        rw [← this]; module
      have hs_eq : s = (1 - τ) * ra + τ * rb := by
        rcases smul_eq_zero.1 e'' with h0 | h0
        · linarith
        · exact absurd h0 hd0
      have : (1 - τ) * ra + τ * rb < 0 := by
        rcases hτ.1.lt_or_eq with h0 | h0
        · have := mul_neg_of_pos_of_neg h0 hrb0
          have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hτ.2) hra0.le
          linarith
        · rw [← h0]; linarith
      linarith

end cyc

variable {m : ℕ}

/-- for every point which is not a vertex there is a ray (even a line) without vertices -/
theorem exists_generic_ray (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ} (hx : x ∉ boundary v) :
    ∃ d : ℝ × ℝ, d ≠ 0 ∧ ∀ k, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v k := by
  have hxv : ∀ i, x ≠ v i :=
    fun i h => hx (mem_iUnion.2 ⟨i, h ▸ left_mem_segment ℝ _ _⟩)
  obtain ⟨d, hd0, hd⟩ := exists_generic_dir v hxv
  exact ⟨d, hd0, fun k s _ => hd k s⟩

/-- **Ray-crossing parity.**  Let `v` be a simple closed polygon, `x` a point off the curve
and `d ≠ 0` a direction such that the ray `{x + s • d | s ≥ 0}` contains no vertex.  Then
`x ∈ region v` iff the ray meets an odd number of sides. -/
theorem mem_region_iff_odd_crossings (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x d : ℝ × ℝ} (hx : x ∉ boundary v) (hd0 : d ≠ 0)
    (hd : ∀ k, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v k) :
    x ∈ region v ↔ Odd {k | ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ side v k}.ncard := by
  have hx' := hx
  rw [boundary_eq] at hx'
  have h := ray_parity hv.simple hd0 _ x hx' hd rfl
  simp only [rot_apply, ← windingNumber_eq] at h
  unfold side
  rw [← h]
  constructor
  · rintro (hb | hw)
    · exact absurd hb hx
    · exact hw
  · exact fun hw => Or.inr hw

/-- under the hypotheses of `mem_region_iff_odd_crossings`, every side meets the ray in at most
one point: the number of sides met is the number of crossing points -/
theorem ray_side_unique (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x d : ℝ × ℝ} (hx : x ∉ boundary v) (hd : ∀ k, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v k)
    (k : Fin (m + 3)) {s s' : ℝ} (hs0 : 0 ≤ s) (hs0' : 0 ≤ s')
    (h : x + s • d ∈ side v k) (h' : x + s' • d ∈ side v k) : s = s' := by
  rw [boundary_eq] at hx
  have := ray_side_subsingleton hv.simple hx hd k hs0 hs0'
  simp only [rot_apply] at this
  exact this h h'

end

end Stein.Polygon
