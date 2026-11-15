import Stein.Polygon.Jordan

/-!
# The region of a simple closed polygon and the bounded component of its complement, over `ℂ`

A definition of the region bounded by a closed polygonal curve which does not use winding
numbers, stated in `ℂ`, and its agreement with `region` (`Stein/Polygon/Region.lean`).

* `polyCurve v` : the closed polygonal curve with vertices `v : Fin n → ℂ`.
* `polyInterior v` : the points off the curve whose connected component in the complement of the
  curve is bounded.
* `toC_image_boundary` : `toC '' boundary v = polyCurve (toC ∘ v)`.
* `windingNumber_ne_zero_subset_polyInterior` (easy half, any closed polygonal curve).
* `polyInterior_subset_windingNumber_ne_zero` (hard half, simple closed polygons; uses the
  polygonal Jordan curve theorem of `Stein/Polygon/Jordan.lean`).
* `region_eq_polyInterior` : for a simple closed polygon,
  `region v = boundary v ∪ toC ⁻¹' polyInterior (toC ∘ v)`; `toC_image_region` is the same
  statement in `ℂ`.

These statements are not used in the proof of the main theorem.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

/-- the closed polygonal curve with vertices `v k` (indices mod `n`) -/
def polyCurve {n : ℕ} [NeZero n] (v : Fin n → ℂ) : Set ℂ :=
  ⋃ k, segment ℝ (v k) (v (k + 1))

/-- the interior of a closed polygonal curve: the points off the curve whose connected component
in the complement of the curve is bounded -/
def polyInterior {n : ℕ} [NeZero n] (v : Fin n → ℂ) : Set ℂ :=
  {p | p ∉ polyCurve v ∧ Bornology.IsBounded (connectedComponentIn (polyCurve v)ᶜ p)}

/-- `toC` as a continuous linear equivalence -/
private def toCL : (ℝ × ℝ) ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm

/-- `toCL` is `toC`. -/
private theorem toCL_apply (p : ℝ × ℝ) : toCL p = toC p := by
  rw [toCL, Complex.equivRealProdCLM_symm_apply, toC]

/-- `toCL` is `toC`, as functions. -/
private theorem coe_toCL : ⇑toCL = toC := funext toCL_apply

/-- The identification `toC : ℝ × ℝ → ℂ` is bijective. -/
theorem toC_bijective : Function.Bijective toC := by
  rw [← coe_toCL]; exact toCL.bijective

/-- `toC` maps segments to segments. -/
private theorem toC_image_segment (a b : ℝ × ℝ) :
    toC '' segment ℝ a b = segment ℝ (toC a) (toC b) := by
  have := image_segment ℝ (toCL : (ℝ × ℝ) →ₗ[ℝ] ℂ).toAffineMap a b
  simpa [coe_toCL] using this

/-- A set is bounded iff its image under `toC` is bounded. -/
private theorem isBounded_toC_image {s : Set (ℝ × ℝ)} :
    Bornology.IsBounded (toC '' s) ↔ Bornology.IsBounded s := by
  rw [← coe_toCL]
  constructor
  · intro h
    have := (toCL.symm : ℂ →L[ℝ] ℝ × ℝ).lipschitzWith.isBounded_image h
    rwa [ContinuousLinearEquiv.coe_coe, toCL.symm_image_image] at this
  · intro h
    exact (toCL : (ℝ × ℝ) →L[ℝ] ℂ).lipschitzWith.isBounded_image h

variable {m : ℕ}

/-- the curve over `ℂ` is the image of the curve over `ℝ × ℝ` -/
theorem toC_image_boundary (v : Fin (m + 3) → ℝ × ℝ) :
    toC '' boundary v = polyCurve (toC ∘ v) := by
  simp only [boundary, side, polyCurve, image_iUnion, toC_image_segment, Function.comp_apply]

/-- Membership in `polyCurve`, read in `ℝ × ℝ`. -/
theorem toC_mem_polyCurve (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ} :
    toC x ∈ polyCurve (toC ∘ v) ↔ x ∈ boundary v := by
  rw [← toC_image_boundary]
  exact toC_bijective.injective.mem_set_image

/-- membership in `polyInterior`, read in `ℝ × ℝ` (any closed polygonal curve) -/
theorem toC_mem_polyInterior (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ} :
    toC x ∈ polyInterior (toC ∘ v) ↔
      x ∉ boundary v ∧ Bornology.IsBounded (connectedComponentIn (boundary v)ᶜ x) := by
  unfold polyInterior
  rw [mem_ofPred_eq, toC_mem_polyCurve]
  apply and_congr_right
  intro hx
  have e1 : (polyCurve (toC ∘ v))ᶜ = toC '' (boundary v)ᶜ := by
    rw [image_compl_eq toC_bijective, toC_image_boundary]
  have e2 := toCL.toHomeomorph.image_connectedComponentIn (s := (boundary v)ᶜ) (x := x) hx
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, coe_toCL] at e2
  rw [e1, ← e2, isBounded_toC_image]

/-- **easy half (any closed polygonal curve).**  The points off the curve with non-zero winding
number belong to `polyInterior`. -/
theorem windingNumber_ne_zero_subset_polyInterior (v : Fin (m + 3) → ℝ × ℝ) :
    {x | windingNumber v x ≠ 0} \ boundary v ⊆ toC ⁻¹' polyInterior (toC ∘ v) := by
  rintro x ⟨hw, hb⟩
  exact (toC_mem_polyInterior v).2 ⟨hb, isBounded_component_of_ne_zero v hb hw⟩

/-- **hard half (simple closed polygons; the Jordan part).**  The points of `polyInterior` have
non-zero winding number: no bounded component of the complement of the curve has winding number
zero. -/
theorem polyInterior_subset_windingNumber_ne_zero (v : Fin (m + 3) → ℝ × ℝ)
    (hv : SimplePolygon v) :
    toC ⁻¹' polyInterior (toC ∘ v) ⊆ {x | windingNumber v x ≠ 0} \ boundary v := by
  intro x hx
  obtain ⟨hb, hbd⟩ := (toC_mem_polyInterior v).1 hx
  exact ⟨fun hw => not_isBounded_component_of_eq_zero v hv hb hw hbd, hb⟩

/-- for a simple closed polygon, `polyInterior` is the set of the points off the curve with
non-zero winding number, i.e. `region v \ boundary v`, the interior of `region v` -/
theorem preimage_polyInterior (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    toC ⁻¹' polyInterior (toC ∘ v) = region v \ boundary v := by
  rw [region_diff_boundary]
  apply Subset.antisymm
  · intro x hx
    have := polyInterior_subset_windingNumber_ne_zero v hv hx
    exact ⟨this.2, this.1⟩
  · intro x hx
    exact windingNumber_ne_zero_subset_polyInterior v ⟨hx.2, hx.1⟩

/-- **The winding-number region of a simple closed polygon is the curve together with
`polyInterior`.** -/
theorem region_eq_polyInterior (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    region v = boundary v ∪ toC ⁻¹' polyInterior (toC ∘ v) := by
  rw [preimage_polyInterior v hv, union_sdiff_self, union_eq_right.2 (boundary_subset_region v)]

/-- the same statement in `ℂ` -/
theorem toC_image_region (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    toC '' region v = polyCurve (toC ∘ v) ∪ polyInterior (toC ∘ v) := by
  rw [region_eq_polyInterior v hv, image_union, toC_image_boundary,
    image_preimage_eq _ toC_bijective.surjective]

end

end Stein.Polygon
