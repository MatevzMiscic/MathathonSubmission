import Stein.Polygon.Components

/-!
# The polygonal Jordan curve theorem

`v : Fin (m + 3) → ℝ × ℝ`, `boundary v` the closed polygonal curve, `region v` the curve together
with the points of non-zero winding number (`Stein/Polygon/Region.lean`).  For a simple closed
polygon (`SimplePolygon v`):

* `windingNumber_values` : off the curve the winding number is `0` or `ε`, for one `ε ∈ {1, -1}`;
* `isConnected_inner`, `isConnected_outer` : `region v \ boundary v` and `(region v)ᶜ` are
  connected (and open, non-empty, the first bounded, the second unbounded): they are the two
  connected components of the complement of the curve (`connectedComponentIn_of_ne_zero`,
  `connectedComponentIn_of_eq_zero`, `jordan`);
* `closure_inner`, `interior_region`, `frontier_inner`, `frontier_outer` : closure, interior and
  topological boundary of the inside and of the outside;
* `region_eq_bounded` : `region v` is the curve together with the points whose connected
  component in the complement of the curve is bounded.

These statements are not used in the proof of the main theorem; they show that `region v` is the
closed region bounded by the polygon `v` in the usual sense.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- every point of the curve is a limit of points off the curve on its left, and of points off
the curve on its right -/
private theorem curve_subset_closure (hs : Simple v σ) {l : ℤ}
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l)
    {e : ℝ} (he : e ≠ 0) :
    curveCyc v σ ⊆ closure {x | x ∉ curveCyc v σ ∧ wind v σ x = sideWind l e} := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  have hopen : openSegment ℝ (v k) (v (σ k)) ⊆
      closure {x | x ∉ curveCyc v σ ∧ wind v σ x = sideWind l e} := by
    intro y hy
    rw [openSegment_eq_pt] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [mem_closure_iff_frequently]
    exact ((freq_side (hs.ne k) (cross_pt _ _ t) he).and_eventually
      (side_witness hs hl k ht he)).mono (fun y hy => ⟨(hy.2 hy.1).1, (hy.2 hy.1).2.2⟩)
  have := isClosed_closure.closure_subset_iff.2 hopen
  rw [closure_openSegment] at this
  exact this hk

/-- **The values of the winding number of a simple closed polygonal curve** (general index type):
off the curve it is `0` or `ε`, for one sign `ε ∈ {1, -1}`; both values occur, and every point
of the curve is a limit of points with either value. -/
theorem wind_values (hs : Simple v σ) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (∀ x, x ∉ curveCyc v σ → wind v σ x = 0 ∨ wind v σ x = ε) ∧
      (∃ x, x ∉ curveCyc v σ ∧ wind v σ x = ε) ∧
      (∃ x, x ∉ curveCyc v σ ∧ wind v σ x = 0) ∧
      curveCyc v σ ⊆ closure {x | x ∉ curveCyc v σ ∧ wind v σ x = ε} ∧
      curveCyc v σ ⊆ closure {x | x ∉ curveCyc v σ ∧ wind v σ x = 0} := by
  have e1 : ∀ l : ℤ, sideWind l 1 = l := fun l => by simp [sideWind]
  have e2 : ∀ l : ℤ, sideWind l (-1) = l - 1 := fun l => by simp [sideWind]
  rcases wind_side_cases hs with hl | hl
  · have c1 := curve_subset_closure hs hl (e := 1) one_ne_zero
    have c2 := curve_subset_closure hs hl (e := -1) (by norm_num)
    rw [e1] at c1
    rw [e2, sub_self] at c2
    have hx := exists_wind_eq hs hl
    rw [sub_self] at hx
    refine ⟨1, Or.inl rfl, fun x hx => ?_, hx.1, hx.2, c1, c2⟩
    rcases wind_mem_pair hs (Or.inl rfl) hl hx with h | h
    · right; exact h
    · left; rw [h]; norm_num
  · have c1 := curve_subset_closure hs hl (e := 1) one_ne_zero
    have c2 := curve_subset_closure hs hl (e := -1) (by norm_num)
    rw [e1] at c1
    rw [e2, zero_sub] at c2
    have hx := exists_wind_eq hs hl
    rw [zero_sub] at hx
    refine ⟨-1, Or.inr rfl, fun x hx => ?_, hx.2, hx.1, c2, c1⟩
    rcases wind_mem_pair hs (Or.inr rfl) hl hx with h | h
    · left; exact h
    · right; rw [h]; norm_num

end cyc

variable {m : ℕ}

/-! ### The values of the winding number -/

/-- **Off the curve, the winding number of a simple closed polygon is `0` or `ε`**, for one
sign `ε ∈ {1, -1}` (`ε = 1`: counter-clockwise polygon); both values occur. -/
theorem windingNumber_values (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (∀ x, x ∉ boundary v → windingNumber v x = 0 ∨ windingNumber v x = ε) ∧
      (∃ x, x ∉ boundary v ∧ windingNumber v x = ε) ∧
      (∃ x, x ∉ boundary v ∧ windingNumber v x = 0) := by
  obtain ⟨ε, h1, h2, h3, h4, -, -⟩ := wind_values hv.simple
  refine ⟨ε, h1, ?_, ?_, ?_⟩
  · simpa only [boundary_eq, windingNumber_eq] using h2
  · simpa only [boundary_eq, windingNumber_eq] using h3
  · simpa only [boundary_eq, windingNumber_eq] using h4

/-- the winding number is constant on connected sets which do not meet the curve (any `v`) -/
theorem windingNumber_const_on (v : Fin (m + 3) → ℝ × ℝ) {S : Set (ℝ × ℝ)}
    (hS : IsPreconnected S) (hSU : S ⊆ (boundary v)ᶜ) {x y : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    windingNumber v x = windingNumber v y := by
  rw [boundary_eq] at hSU
  rw [windingNumber_eq, windingNumber_eq]
  exact wind_const_on hS hSU hx hy

/-! ### The two components of the complement of the curve -/

/-- The inside `region v \ boundary v` is the set of the points off the curve with non-zero
winding number. -/
theorem region_diff_boundary (v : Fin (m + 3) → ℝ × ℝ) :
    region v \ boundary v = {x | x ∉ boundary v ∧ windingNumber v x ≠ 0} := by
  ext x
  simp only [region, Set.mem_sdiff, mem_union, mem_ofPred_eq]
  tauto

/-- The outside `(region v)ᶜ` is the set of the points off the curve with winding number zero. -/
theorem compl_region (v : Fin (m + 3) → ℝ × ℝ) :
    (region v)ᶜ = {x | x ∉ boundary v ∧ windingNumber v x = 0} := by
  ext x
  simp only [region, mem_compl_iff, mem_union, mem_ofPred_eq]
  tauto

/-- The closed polygonal curve is a closed set. -/
theorem isClosed_boundary (v : Fin (m + 3) → ℝ × ℝ) : IsClosed (boundary v) := by
  rw [boundary_eq]; exact isClosed_curveCyc _ _

/-- The outside `(region v)ᶜ` is open. -/
theorem isOpen_outer (v : Fin (m + 3) → ℝ × ℝ) : IsOpen (region v)ᶜ :=
  (isClosed_region v).isOpen_compl

/-- the interior of the region is the region without the curve -/
theorem interior_region (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    interior (region v) = region v \ boundary v := by
  rw [← frontier_region v hv, (isClosed_region v).frontier_eq, sdiff_sdiff_right_self,
    inter_eq_right.2 interior_subset]

/-- The inside `region v \ boundary v` of a simple closed polygon is open. -/
theorem isOpen_inner (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    IsOpen (region v \ boundary v) := by
  rw [← interior_region v hv]; exact isOpen_interior

/-- The inside `region v \ boundary v` is bounded. -/
theorem isBounded_inner (v : Fin (m + 3) → ℝ × ℝ) :
    Bornology.IsBounded (region v \ boundary v) :=
  (isCompact_region v).isBounded.subset sdiff_subset

/-- The outside `(region v)ᶜ` is unbounded. -/
theorem not_isBounded_outer (v : Fin (m + 3) → ℝ × ℝ) : ¬ Bornology.IsBounded (region v)ᶜ := by
  intro h
  have hu : Bornology.IsBounded (univ : Set (ℝ × ℝ)) := by
    have := (isCompact_region v).isBounded.union h
    rwa [union_compl_self] at this
  obtain ⟨S₀, -, hS⟩ := ray_leaves hu (0 : ℝ × ℝ) (d := (1, 0)) (by simp)
  exact hS S₀ le_rfl (mem_univ _)

/-- **the inside `region v \ boundary v` of a simple closed polygon is connected** -/
theorem isConnected_inner (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    IsConnected (region v \ boundary v) := by
  obtain ⟨ε, h1, h2, ⟨x, hx, hxw⟩, -⟩ := windingNumber_values v hv
  have hε : ε ≠ 0 := by rcases h1 with h | h <;> rw [h] <;> norm_num
  have e : region v \ boundary v =
      {x | x ∉ curveCyc v (finRotate (m + 3)) ∧ wind v (finRotate (m + 3)) x = ε} := by
    rw [region_diff_boundary]
    ext y
    simp only [mem_ofPred_eq, ← boundary_eq, ← windingNumber_eq]
    constructor
    · rintro ⟨hy, hw⟩
      rcases h2 y hy with h | h
      · exact absurd h hw
      · exact ⟨hy, h⟩
    · rintro ⟨hy, hw⟩
      exact ⟨hy, by rw [hw]; exact hε⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [region_diff_boundary]; exact ⟨hx, by rw [hxw]; exact hε⟩
  · rw [e]; exact isPreconnected_wind_eq hv.simple ε

/-- **the outside `(region v)ᶜ` of a simple closed polygon is connected** -/
theorem isConnected_outer (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    IsConnected (region v)ᶜ := by
  obtain ⟨ε, -, -, -, ⟨x, hx, hxw⟩⟩ := windingNumber_values v hv
  have e : (region v)ᶜ =
      {x | x ∉ curveCyc v (finRotate (m + 3)) ∧ wind v (finRotate (m + 3)) x = 0} := by
    rw [compl_region]
    ext y
    simp only [mem_ofPred_eq, ← boundary_eq, ← windingNumber_eq]
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [compl_region]; exact ⟨hx, hxw⟩
  · rw [e]; exact isPreconnected_wind_eq hv.simple 0

/-- the connected component (in the complement of the curve) of a point of non-zero winding
number is the inside -/
theorem connectedComponentIn_of_ne_zero (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x : ℝ × ℝ} (hx : x ∉ boundary v) (hw : windingNumber v x ≠ 0) :
    connectedComponentIn (boundary v)ᶜ x = region v \ boundary v := by
  apply Subset.antisymm
  · intro y hy
    rw [region_diff_boundary]
    refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
    rw [windingNumber_const_on v isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hy (mem_connectedComponentIn hx)]
    exact hw
  · apply (isConnected_inner v hv).isPreconnected.subset_connectedComponentIn
    · rw [region_diff_boundary]; exact ⟨hx, hw⟩
    · exact fun y hy => hy.2

/-- the connected component (in the complement of the curve) of a point off the curve of winding
number zero is the outside -/
theorem connectedComponentIn_of_eq_zero (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x : ℝ × ℝ} (hx : x ∉ boundary v) (hw : windingNumber v x = 0) :
    connectedComponentIn (boundary v)ᶜ x = (region v)ᶜ := by
  apply Subset.antisymm
  · intro y hy
    rw [compl_region]
    refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
    rw [windingNumber_const_on v isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) hy (mem_connectedComponentIn hx)]
    exact hw
  · apply (isConnected_outer v hv).isPreconnected.subset_connectedComponentIn
    · rw [compl_region]; exact ⟨hx, hw⟩
    · exact fun y hy hb => hy (boundary_subset_region v hb)

/-- **Polygonal Jordan curve theorem.**  The complement of a simple closed polygon is the
disjoint union of the two non-empty connected open sets `region v \ boundary v` (bounded) and
`(region v)ᶜ` (unbounded); hence these are its two connected components. -/
theorem jordan (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    (boundary v)ᶜ = (region v \ boundary v) ∪ (region v)ᶜ ∧
    Disjoint (region v \ boundary v) (region v)ᶜ ∧
    IsConnected (region v \ boundary v) ∧ IsConnected (region v)ᶜ ∧
    IsOpen (region v \ boundary v) ∧ IsOpen (region v)ᶜ ∧
    Bornology.IsBounded (region v \ boundary v) ∧ ¬ Bornology.IsBounded (region v)ᶜ := by
  refine ⟨?_, ?_, isConnected_inner v hv, isConnected_outer v hv, isOpen_inner v hv,
    isOpen_outer v, isBounded_inner v, not_isBounded_outer v⟩
  · ext x
    have := @boundary_subset_region _ v x
    simp only [mem_compl_iff, mem_union, Set.mem_sdiff]
    tauto
  · exact disjoint_compl_right.mono_left sdiff_subset

/-- every connected component of the complement of the curve is the inside or the outside -/
theorem connectedComponentIn_cases (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x : ℝ × ℝ} (hx : x ∉ boundary v) :
    connectedComponentIn (boundary v)ᶜ x = region v \ boundary v ∨
      connectedComponentIn (boundary v)ᶜ x = (region v)ᶜ := by
  by_cases hw : windingNumber v x = 0
  · exact Or.inr (connectedComponentIn_of_eq_zero v hv hx hw)
  · exact Or.inl (connectedComponentIn_of_ne_zero v hv hx hw)

/-- the region is the closure of the inside -/
theorem closure_inner (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    closure (region v \ boundary v) = region v := by
  apply Subset.antisymm
  · exact (isClosed_region v).closure_subset_iff.2 sdiff_subset
  · obtain ⟨ε, h1, h2, -, -, c1, -⟩ := wind_values hv.simple
    have hε : ε ≠ 0 := by rcases h1 with h | h <;> rw [h] <;> norm_num
    have hsub : {x | x ∉ curveCyc v (finRotate (m + 3)) ∧ wind v (finRotate (m + 3)) x = ε} ⊆
        region v \ boundary v := by
      rw [region_diff_boundary]
      rintro y ⟨hy, hw⟩
      simp only [mem_ofPred_eq, boundary_eq, windingNumber_eq]
      exact ⟨hy, by rw [hw]; exact hε⟩
    intro x hx
    by_cases hb : x ∈ boundary v
    · rw [boundary_eq] at hb
      exact closure_mono hsub (c1 hb)
    · exact subset_closure ⟨hx, hb⟩

/-- the curve is the topological boundary of the inside -/
theorem frontier_inner (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    frontier (region v \ boundary v) = boundary v := by
  rw [frontier, closure_inner v hv, (isOpen_inner v hv).interior_eq, sdiff_sdiff_right_self,
    inter_eq_right.2 (boundary_subset_region v)]

/-- the curve is the topological boundary of the outside -/
theorem frontier_outer (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    frontier (region v)ᶜ = boundary v := by
  rw [frontier_compl, frontier_region v hv]

/-! ### The region as "the curve and the bounded components of its complement" -/

/-- **easy half (any closed polygonal curve)**: a point off the curve with non-zero winding
number lies in a bounded component of the complement of the curve -/
theorem isBounded_component_of_ne_zero (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ}
    (hx : x ∉ boundary v) (hw : windingNumber v x ≠ 0) :
    Bornology.IsBounded (connectedComponentIn (boundary v)ᶜ x) := by
  apply (isCompact_region v).isBounded.subset
  intro y hy
  right
  show windingNumber v y ≠ 0
  rw [windingNumber_const_on v isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) hy (mem_connectedComponentIn hx)]
  exact hw

/-- **hard half (simple closed polygons; Jordan)**: the component of a point off the curve with
winding number zero is unbounded -/
theorem not_isBounded_component_of_eq_zero (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    {x : ℝ × ℝ} (hx : x ∉ boundary v) (hw : windingNumber v x = 0) :
    ¬ Bornology.IsBounded (connectedComponentIn (boundary v)ᶜ x) := by
  rw [connectedComponentIn_of_eq_zero v hv hx hw]
  exact not_isBounded_outer v

/-- **the region bounded by a simple closed polygon is the curve together with the bounded
connected components of its complement** (equivalently: the complement of the unbounded
component) -/
theorem region_eq_bounded (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    region v = boundary v ∪
      {x | x ∉ boundary v ∧ Bornology.IsBounded (connectedComponentIn (boundary v)ᶜ x)} := by
  ext x
  constructor
  · rintro (hb | hw)
    · exact Or.inl hb
    · by_cases hb : x ∈ boundary v
      · exact Or.inl hb
      · exact Or.inr ⟨hb, isBounded_component_of_ne_zero v hb hw⟩
  · rintro (hb | ⟨hb, hbd⟩)
    · exact Or.inl hb
    · right
      intro hw
      exact not_isBounded_component_of_eq_zero v hv hb hw hbd

end

end Stein.Polygon
