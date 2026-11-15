import Stein.Polygon.Region

/-!
# The region of a simple closed polygon: compactness and topological boundary

Basic topological properties of `Stein.Polygon.region v` (the polygonal curve together with the
points of non-zero winding number), which show that it is the closed region bounded by the simple
closed polygon `v`:

* `boundary_subset_region` : the curve is contained in the region;
* `region_subset_Icc` : the region is contained in every axis-parallel box containing the vertices;
* `isClosed_region`, `isCompact_region` : the region is closed and bounded;
* `frontier_region` : for a simple closed polygon, the topological boundary of the region is the
  polygonal curve.

The first part of the file proves these statements for closed polygonal curves with an arbitrary
finite index type and successor permutation `σ` (`regionCyc_subset_Icc`, `isClosed_regionCyc`,
`isCompact_regionCyc`, `frontier_regionCyc`).
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

/-! ### Closed polygonal curves with a successor permutation -/

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- if all vertices lie strictly on one side of a line through `x` (i.e. for some complex number
`c` all `c * (v j - x)` have positive real part), the angle sum at `x` vanishes -/
theorem angSum_eq_zero_of_dir (σ : ι ≃ ι) {x : ℝ × ℝ} (c : ℂ)
    (h : ∀ j, 0 < (c * (toC (v j) - toC x)).re) : angSum v σ x = 0 := by
  set ψ : ι → ℝ := fun j => arg (c * (toC (v j) - toC x)) with hψ
  have hb : ∀ j, |ψ j| < Real.pi / 2 := fun j => abs_arg_lt_pi_div_two_iff.2 (Or.inl (h j))
  have hne : ∀ j, c * (toC (v j) - toC x) ≠ 0 := by
    intro j h0
    have := h j
    rw [h0] at this
    simp at this
  have hang : ∀ j, ang (v j) (v (σ j)) x = ψ (σ j) - ψ j := by
    intro j
    have hc : c ≠ 0 := fun h0 => hne j (by rw [h0, zero_mul])
    have e : zq (v j) (v (σ j)) x =
        (c * (toC (v (σ j)) - toC x)) / (c * (toC (v j) - toC x)) := by
      rw [zq, mul_div_mul_left _ _ hc]
    have h1 := abs_lt.1 (hb j)
    have h2 := abs_lt.1 (hb (σ j))
    unfold ang
    rw [e]
    exact arg_div_eq (hne (σ j)) (hne j) ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
      by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  unfold angSum
  simp only [hang]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp σ ψ, sub_self]

/-- if all vertices lie strictly on one side of a line through `x`, the winding number around `x`
vanishes -/
theorem wind_eq_zero_of_dir (σ : ι ≃ ι) {x : ℝ × ℝ} (c : ℂ)
    (h : ∀ j, 0 < (c * (toC (v j) - toC x)).re) : wind v σ x = 0 := by
  unfold wind
  rw [angSum_eq_zero_of_dir σ c h, zero_div, round_zero]

/-- the region is contained in every box containing the vertices -/
theorem regionCyc_subset_Icc (σ : ι ≃ ι) (lo hi : ℝ × ℝ) (h : ∀ j, v j ∈ Icc lo hi) :
    regionCyc v σ ⊆ Icc lo hi := by
  rintro x (hx | hx)
  · obtain ⟨i, hi'⟩ := mem_iUnion.1 hx
    exact (convex_Icc lo hi).segment_subset (h i) (h (σ i)) hi'
  · by_contra hbox
    apply hx
    have hv : ∀ j, lo.1 ≤ (v j).1 ∧ lo.2 ≤ (v j).2 ∧ (v j).1 ≤ hi.1 ∧ (v j).2 ≤ hi.2 :=
      fun j => ⟨(h j).1.1, (h j).1.2, (h j).2.1, (h j).2.2⟩
    have hcases : x.1 < lo.1 ∨ x.2 < lo.2 ∨ hi.1 < x.1 ∨ hi.2 < x.2 := by
      by_contra hn
      simp only [not_or, not_lt] at hn
      exact hbox ⟨⟨hn.1, hn.2.1⟩, ⟨hn.2.2.1, hn.2.2.2⟩⟩
    rcases hcases with h1 | h1 | h1 | h1
    · apply wind_eq_zero_of_dir σ 1
      intro j; simp; linarith [(hv j).1]
    · apply wind_eq_zero_of_dir σ (-I)
      intro j; simp; linarith [(hv j).2.1]
    · apply wind_eq_zero_of_dir σ (-1)
      intro j; simp; linarith [(hv j).2.2.1]
    · apply wind_eq_zero_of_dir σ I
      intro j; simp; linarith [(hv j).2.2.2]

/-- the region bounded by a closed polygonal curve is closed -/
theorem isClosed_regionCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : IsClosed (regionCyc v σ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hoff : ∀ i, x ∉ segment ℝ (v i) (v (σ i)) :=
    fun i hi => hx (Or.inl (mem_iUnion.2 ⟨i, hi⟩))
  rcases region_off v σ hoff with h | h
  · exact absurd h.self_of_nhds hx
  · exact h

/-- the region bounded by a closed polygonal curve is compact -/
theorem isCompact_regionCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : IsCompact (regionCyc v σ) := by
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range v
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range v
  have hsub := regionCyc_subset_Icc σ lo hi
    (fun j => ⟨hlo (mem_range_self j), hhi (mem_range_self j)⟩)
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_regionCyc v σ)
    ((Metric.isBounded_Icc lo hi).subset hsub)

/-- the square of the distance of two different points is positive -/
theorem sqdist_pos {a b : ℝ × ℝ} (hab : a ≠ b) : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
  by_contra h
  have h1 : (b.1 - a.1) ^ 2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
  have h2 : (b.2 - a.2) ^ 2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
  apply hab
  apply Prod.ext
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 h1; linarith
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 h2; linarith

/-- arbitrarily close to a point of the line `a b` there are points strictly on its right, and
points strictly on its left -/
theorem frequently_cross {a b x : ℝ × ℝ} (hab : a ≠ b) (hx : cross a b x = 0) :
    (∃ᶠ y in 𝓝 x, cross a b y < 0) ∧ (∃ᶠ y in 𝓝 x, 0 < cross a b y) := by
  have hd := sqdist_pos hab
  set n : ℝ × ℝ := (b.2 - a.2, -(b.1 - a.1)) with hn
  have hcr : ∀ δ : ℝ, cross a b (x + δ • n) = -δ * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    intro δ
    unfold cross at hx ⊢
    simp only [hn, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination hx
  have hc : Continuous (fun δ : ℝ => x + δ • n) := by fun_prop
  have h0 : Tendsto (fun δ : ℝ => x + δ • n) (𝓝 0) (𝓝 x) := by
    have := hc.tendsto 0
    simpa using this
  constructor
  · apply (h0.mono_left (nhdsWithin_le_nhds (s := Ioi 0))).frequently
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hcr]
    have : 0 < δ := hδ
    nlinarith
  · apply (h0.mono_left (nhdsWithin_le_nhds (s := Iio 0))).frequently
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hcr]
    have : δ < 0 := hδ
    nlinarith

/-- **for a simple closed polygon, the topological boundary of the region is the curve** -/
theorem frontier_regionCyc (hs : Simple v σ) : frontier (regionCyc v σ) = curveCyc v σ := by
  have hcl := isClosed_regionCyc v σ
  apply Subset.antisymm
  · intro x hx
    by_contra hxc
    have hoff : ∀ i, x ∉ segment ℝ (v i) (v (σ i)) :=
      fun i hi => hxc (mem_iUnion.2 ⟨i, hi⟩)
    rcases region_off v σ hoff with h | h
    · exact hx.2 (mem_interior_iff_mem_nhds.2 h)
    · have := mem_closure_iff_frequently.1 hx.1
      exact this h
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    have hopen : openSegment ℝ (v k) (v (σ k)) ⊆ frontier (regionCyc v σ) := by
      intro y hy
      rw [openSegment_eq_pt] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      have hon : pt (v k) (v (σ k)) t ∈ regionCyc v σ :=
        Or.inl (mem_iUnion.2 ⟨k, pt_mem_segment _ _ ht.1.le ht.2.le⟩)
      refine ⟨subset_closure hon, fun hint => ?_⟩
      have hev := mem_interior_iff_mem_nhds.1 hint
      have hc0 : cross (v k) (v (σ k)) (pt (v k) (v (σ k)) t) = 0 :=
        cross_of_mem_segment (pt_mem_segment _ _ ht.1.le ht.2.le)
      obtain ⟨f1, f2⟩ := frequently_cross (hs.ne k) hc0
      rcases region_side hs with h | h
      · have := (f1.and_eventually ((h k t ht).and hev)).exists
        obtain ⟨y, hy1, hy2, hy3⟩ := this
        exact hy2.2 hy1 hy3
      · have := (f2.and_eventually ((h k t ht).and hev)).exists
        obtain ⟨y, hy1, hy2, hy3⟩ := this
        exact hy2.1 hy1 hy3
    have := isClosed_frontier.closure_subset_iff.2 hopen
    rw [closure_openSegment] at this
    exact this hk

end cyc

/-! ### Polygons `v : Fin (m + 3) → ℝ × ℝ` -/

variable {m : ℕ}

/-- the polygonal curve is contained in the region -/
theorem boundary_subset_region (v : Fin (m + 3) → ℝ × ℝ) : boundary v ⊆ region v :=
  subset_union_left

/-- `boundary v` is the curve `curveCyc v σ` for the cyclic successor `σ = finRotate (m + 3)` -/
theorem boundary_eq (v : Fin (m + 3) → ℝ × ℝ) : boundary v = curveCyc v (finRotate (m + 3)) := by
  simp only [boundary, curveCyc, side, rot_apply]

/-- the region is contained in every axis-parallel box containing the vertices -/
theorem region_subset_Icc (v : Fin (m + 3) → ℝ × ℝ) (lo hi : ℝ × ℝ) (h : ∀ j, v j ∈ Icc lo hi) :
    region v ⊆ Icc lo hi := by
  rw [region_eq]; exact regionCyc_subset_Icc _ lo hi h

/-- the region is closed -/
theorem isClosed_region (v : Fin (m + 3) → ℝ × ℝ) : IsClosed (region v) := by
  rw [region_eq]; exact isClosed_regionCyc _ _

/-- the region is compact -/
theorem isCompact_region (v : Fin (m + 3) → ℝ × ℝ) : IsCompact (region v) := by
  rw [region_eq]; exact isCompact_regionCyc _ _

/-- for a simple closed polygon, the topological boundary of `region v` is the polygonal curve -/
theorem frontier_region (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    frontier (region v) = boundary v := by
  rw [region_eq, boundary_eq]; exact frontier_regionCyc hv.simple

end

end Stein.Polygon
