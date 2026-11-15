import Mathlib

/-!
# Basic definitions

* `Stein.det a b` : the determinant `a.1 * b.2 - a.2 * b.1` of two vectors of `K²`.
* `Stein.par d w` : the vector `w` if `w` is parallel to `d` (`det d w = 0`), and `0` otherwise.
* `Stein.cross a b x = det (b - a) (x - a)` : positive iff `x` is strictly on the left of the
  oriented line `a → b` (real plane).
* `Stein.OrientedBoundary S A B` : the set `S ⊆ ℝ²` lies on the left of its oriented polygonal
  boundary, which consists of the segments `A k → B k`.  This is the only property of a polygon
  used in the proof of the Main Theorem (through the balance lemma, Lemma 4.1 of the paper).
-/

open Set Filter Topology

namespace Stein

/-- The determinant of two plane vectors. -/
def det {K : Type*} [CommRing K] (a b : K × K) : K := a.1 * b.2 - a.2 * b.1

/-- `par d w` is `w` if `w` is parallel to `d`, and `0` otherwise. -/
def par {K : Type*} [CommRing K] [DecidableEq K] (d w : K × K) : K × K :=
  if det d w = 0 then w else 0

/-- `cross a b x = det (b - a) (x - a)`; it is positive iff `x` lies strictly on the left of the
oriented line from `a` to `b`. -/
def cross (a b x : ℝ × ℝ) : ℝ := (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)

/-- `cross a b x` is the determinant of `b - a` and `x - a`. -/
theorem cross_eq_det (a b x : ℝ × ℝ) : cross a b x = det (b - a) (x - a) := rfl

/-- **`S` lies on the left of its oriented polygonal boundary** with sides `A k → B k`:

* `off`  : a point on no side has a neighbourhood contained in `S` or disjoint from `S`;
* `left` : near a point of exactly one side, other than its end points, `S` contains the points
  strictly on the left of the side and no point strictly on its right (the "half-disc" property);
* `fin`  : two different sides have only finitely many common points. -/
structure OrientedBoundary (S : Set (ℝ × ℝ)) {κ : Type*} (A B : κ → ℝ × ℝ) : Prop where
  off : ∀ x, (∀ k, x ∉ segment ℝ (A k) (B k)) →
    (∀ᶠ y in 𝓝 x, y ∈ S) ∨ (∀ᶠ y in 𝓝 x, y ∉ S)
  left : ∀ k x, x ∈ segment ℝ (A k) (B k) → x ≠ A k → x ≠ B k →
    (∀ j, j ≠ k → x ∉ segment ℝ (A j) (B j)) →
    ∀ᶠ y in 𝓝 x, (0 < cross (A k) (B k) y → y ∈ S) ∧ (cross (A k) (B k) y < 0 → y ∉ S)
  fin : ∀ j k, j ≠ k → (segment ℝ (A j) (B j) ∩ segment ℝ (A k) (B k)).Finite

end Stein
