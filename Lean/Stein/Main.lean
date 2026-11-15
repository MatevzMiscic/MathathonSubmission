import Stein.Geometry.Square
import Stein.Polygon.Region

/-!
# The Main Theorem, Stein's conjecture and Monsky's theorem

A polygon with `m + 3` vertices is a map `P : Fin (m + 3) → ℝ × ℝ`; its sides are
`P k → P (k + 1)` (`k + 1` is cyclic in `Fin (m + 3)`).  `Stein.Polygon.SimplePolygon P`
says that the closed polygonal curve is simple, `Stein.Polygon.region P` is the closed region
it bounds (the curve together with the points of non-zero winding number).

* `Stein.SpecialPolygon` : special polygons;
* `Stein.main_theorem` : Theorem 1.2 (Main Theorem);
* `Stein.stein_conjecture`, `Stein.stein_conjecture_fin` : Corollary 1.3 (Stein's conjecture);
* `Stein.monsky`, `Stein.monsky_fin` : Monsky's theorem for the unit square
  `Set.Icc (0 : ℝ × ℝ) 1`;
* `Stein.main_theorem_square` : the Main Theorem for the unit square.

The first three theorems combine the theorems for sets lying on the left of their oriented
boundary (`Stein/Geometry/Dissection.lean`) with `Stein.Polygon.region_orientedBoundary`.  The
proofs of `monsky`, `monsky_fin` and `main_theorem_square` do not use the polygon part
(`Stein/Polygon/`): they only use that the unit square lies on the left of its four sides
(`Stein.square_boundary`, `Stein/Geometry/Square.lean`).
-/

open Set MeasureTheory

namespace Stein

open Stein.Polygon

noncomputable section

variable {m : ℕ}

/-- **Special polygon** (Stein): for every direction `d ≠ 0`, the side vectors `P (k+1) - P k`
that are parallel to `d` sum to `0`.  (`par d w` is `w` if `det d w = 0` and `0` otherwise.)
The condition does not depend on the orientation of the polygon. -/
def SpecialPolygon (P : Fin (m + 3) → ℝ × ℝ) : Prop :=
  ∀ d : ℝ × ℝ, d ≠ 0 → ∑ k, par d (P (k + 1) - P k) = 0

/-- The sides `P k → P (k + 1)` of a special polygon form a special boundary. -/
theorem SpecialPolygon.fwd {P : Fin (m + 3) → ℝ × ℝ} (h : SpecialPolygon P) :
    Special P (fun k => P (k + 1)) := h

/-- The reversed sides `P (k + 1) → P k` of a special polygon form a special boundary. -/
theorem SpecialPolygon.bwd {P : Fin (m + 3) → ℝ × ℝ} (h : SpecialPolygon P) :
    Special (fun k => P (k + 1)) P := by
  intro d hd
  have e : ∀ k, par d (P k - P (k + 1)) = -par d (P (k + 1) - P k) := by
    intro k
    rw [← par_neg, neg_sub]
  simp only [e, Finset.sum_neg_distrib, neg_eq_zero]
  exact h d hd

/-- **Theorem 1.2 (Main Theorem).**  Let `P` be a special simple polygon, `T i` a dissection of
the region bounded by `P` into triangles whose vertices have coordinates in the subfield `K` of
`ℝ`, and `v` any valuation on `K` (multiplicative convention).  If `a i = 2 Area (T i)` and
`a₀ = 2 Area (region P)` (Lebesgue measure) and `v (a i) ≤ γ` for all `i`, then
`v a₀ ≤ v 2 * γ`; additively: `v(2 Area P) ≥ v(2) + min_i v(2 Area T_i)`. -/
theorem main_theorem (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P) (hsp : SpecialPolygon P)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (K : Subfield ℝ) (hK : ∀ i, IsTriangleOver K (T i))
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (γ : Γ₀)
    (a : ι → K) (ha : ∀ i, (a i : ℝ) = 2 * (volume (T i)).toReal) (hγ : ∀ i, v (a i) ≤ γ)
    (a₀ : K) (ha₀ : (a₀ : ℝ) = 2 * (volume (region P)).toReal) :
    v a₀ ≤ v 2 * γ := by
  rcases region_orientedBoundary P hP with h | h
  · exact main_theorem_of_orientedBoundary h hsp.fwd T hT K hK v γ a ha hγ a₀ ha₀
  · exact main_theorem_of_orientedBoundary h hsp.bwd T hT K hK v γ a ha hγ a₀ ha₀

/-- **Corollary 1.3 (Stein's conjecture).**  A special polygon has no equidissection into an odd
number of triangles: if the region bounded by a special simple polygon `P` is dissected into
finitely many triangles `T i` of equal area (Lebesgue measure), then the number of triangles is
even. -/
theorem stein_conjecture (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P) (hsp : SpecialPolygon P)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even (Fintype.card ι) := by
  rcases region_orientedBoundary P hP with h | h
  · exact stein_conjecture_of_orientedBoundary h hsp.fwd T hT heq
  · exact stein_conjecture_of_orientedBoundary h hsp.bwd T hT heq

/-- **Stein's conjecture**, in the form "`n` triangles, each of area `Area P / n`". -/
theorem stein_conjecture_fin (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P)
    (hsp : SpecialPolygon P) {n : ℕ} (T : Fin n → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (heq : ∀ i, volume (T i) = volume (region P) / n) : Even n := by
  simpa using stein_conjecture P hP hsp T hT (fun i j => by rw [heq i, heq j])

/-- **Monsky's theorem.**  The unit square cannot be dissected into an odd number of triangles
of equal area: if finitely many triangles `T i` of equal area (Lebesgue measure) dissect
`[0,1]²`, then their number is even. -/
theorem monsky {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ))
    (hT : IsDissection (Set.Icc (0 : ℝ × ℝ) 1) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even (Fintype.card ι) :=
  stein_conjecture_of_orientedBoundary square_boundary square_special T hT heq

/-- **Monsky's theorem**, for `n` triangles indexed by `Fin n`. -/
theorem monsky_fin {n : ℕ} (T : Fin n → Set (ℝ × ℝ))
    (hT : IsDissection (Set.Icc (0 : ℝ × ℝ) 1) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even n := by
  simpa using monsky T hT heq

/-- **The Main Theorem for the unit square** (`Area = 1`, so `2 Area = 2`): for a dissection of
`[0,1]²` into triangles with vertices in `K²`, and any valuation `v` on `K`, if
`v (2 Area (T i)) ≤ γ` for all `i` then `v 2 ≤ v 2 * γ`. -/
theorem main_theorem_square {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ))
    (hT : IsDissection (Set.Icc (0 : ℝ × ℝ) 1) T)
    (K : Subfield ℝ) (hK : ∀ i, IsTriangleOver K (T i))
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (γ : Γ₀)
    (a : ι → K) (ha : ∀ i, (a i : ℝ) = 2 * (volume (T i)).toReal) (hγ : ∀ i, v (a i) ≤ γ) :
    v 2 ≤ v 2 * γ := by
  have hv : (volume (Set.Icc (0 : ℝ × ℝ) 1)).toReal = 1 := by
    have e : Set.Icc (0 : ℝ × ℝ) 1 = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := Set.Icc_prod_eq 0 1
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  exact main_theorem_of_orientedBoundary square_boundary square_special T hT K hK v γ a ha hγ 2
    (by rw [hv, mul_one]; rfl)

end

end Stein
