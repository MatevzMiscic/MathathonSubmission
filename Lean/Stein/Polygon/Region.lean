import Stein.Polygon.Winding

/-!
# Simple closed polygons: the region they bound has an oriented polygonal boundary

A polygon with `m + 3` vertices is a map `v : Fin (m + 3) → ℝ × ℝ`; the successor `k + 1` in
`Fin (m + 3)` is cyclic, so the sides are `v k → v (k + 1)`.

* `side v k`, `boundary v` : the sides and the closed polygonal curve.
* `SimplePolygon v` : the curve is a simple closed polygon.
* `windingNumber v x` : the winding number of the curve around `x`: the sum of the signed angles
  under which the sides are seen from `x`, divided by `2π`.
* `region v` : the closed region bounded by the curve (the curve and the points around which it
  winds).
* `region_orientedBoundary` : the region of a simple closed polygon lies on the left of all its
  sides `v k → v (k+1)`, or on the left of all reversed sides `v (k+1) → v k`
  (the polygonal Jordan curve theorem, in the form used by the balance lemma).
* `region_orientedBoundary_of_turn` : the first case holds if the polygon turns left at a
  lexicographically smallest vertex.

The proofs are in `Stein/Polygon/Winding.lean`, for closed polygonal curves with an arbitrary finite
index type and successor permutation `σ`; here `σ = finRotate (m + 3)` (`windingNumber_eq`,
`region_eq`, `SimplePolygon.simple`).
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

variable {m : ℕ}

/-- the `k`-th side of the polygon, as a closed segment -/
def side (v : Fin (m + 3) → ℝ × ℝ) (k : Fin (m + 3)) : Set (ℝ × ℝ) :=
  segment ℝ (v k) (v (k + 1))

/-- the closed polygonal curve -/
def boundary (v : Fin (m + 3) → ℝ × ℝ) : Set (ℝ × ℝ) := ⋃ k, side v k

/-- **Simple closed polygon**: the vertices are pairwise distinct, and two different sides have
no common point, except that consecutive sides share their common vertex (and only it). -/
structure SimplePolygon (v : Fin (m + 3) → ℝ × ℝ) : Prop where
  inj : Function.Injective v
  meet : ∀ j k, j ≠ k → ∀ x, x ∈ side v j → x ∈ side v k →
    (k = j + 1 ∧ x = v k) ∨ (j = k + 1 ∧ x = v j)

/-- **Winding number** of the closed polygonal curve around `x`: the sum over the sides
`v k → v (k+1)` of the signed angle in `(-π, π]` under which the side is seen from `x` (the
argument of `(v (k+1) - x) / (v k - x)`, points read as complex numbers), divided by `2π`.
For `x` not a vertex the quotient is an integer (`windingNumber_spec`). -/
def windingNumber (v : Fin (m + 3) → ℝ × ℝ) (x : ℝ × ℝ) : ℤ :=
  round ((∑ k, Complex.arg ((toC (v (k + 1)) - toC x) / (toC (v k) - toC x))) / (2 * Real.pi))

/-- The closed region bounded by the polygonal curve: the curve together with the points around
which it winds. -/
def region (v : Fin (m + 3) → ℝ × ℝ) : Set (ℝ × ℝ) :=
  boundary v ∪ {x | windingNumber v x ≠ 0}

/-- the successor permutation of `Fin (m + 3)` is `i ↦ i + 1` -/
theorem rot_apply (i : Fin (m + 3)) : finRotate (m + 3) i = i + 1 := finRotate_apply i

/-- `windingNumber v` is the winding number `wind v σ` for the cyclic successor
`σ = finRotate (m + 3)` -/
theorem windingNumber_eq (v : Fin (m + 3) → ℝ × ℝ) (x : ℝ × ℝ) :
    windingNumber v x = wind v (finRotate (m + 3)) x := by
  simp only [windingNumber, wind, angSum, ang, zq, rot_apply]

/-- `region v` is the region `regionCyc v σ` for the cyclic successor `σ = finRotate (m + 3)` -/
theorem region_eq (v : Fin (m + 3) → ℝ × ℝ) : region v = regionCyc v (finRotate (m + 3)) := by
  ext x
  simp only [region, regionCyc, boundary, curveCyc, side, windingNumber_eq, rot_apply]

/-- for `x` not a vertex, the sum of the angles is exactly `2π` times the winding number -/
theorem windingNumber_spec (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ} (hx : ∀ k, x ≠ v k) :
    ∑ k, Complex.arg ((toC (v (k + 1)) - toC x) / (toC (v k) - toC x)) =
      2 * Real.pi * windingNumber v x := by
  have h := angSum_eq v (finRotate (m + 3)) hx
  rw [← windingNumber_eq] at h
  simpa only [angSum, ang, zq, rot_apply] using h

private theorem add_one_ne_self (k : Fin (m + 3)) : k + 1 ≠ k := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_add_one] at this
  split_ifs at this with h1
  · rw [h1] at this; simp at this
  · omega

/-- a simple closed polygon `v : Fin (m + 3) → ℝ × ℝ` is a simple closed polygon in the sense of
`Simple`, with the cyclic successor `finRotate (m + 3)` -/
theorem SimplePolygon.simple {v : Fin (m + 3) → ℝ × ℝ} (hv : SimplePolygon v) :
    Simple v (finRotate (m + 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    rw [rot_apply] at h
    exact add_one_ne_self i (hv.inj h).symm
  · intro i j hij x h1 h2
    simp only [rot_apply] at h1 h2 ⊢
    exact hv.meet i j hij x h1 h2
  · refine ⟨0, fun P h0 hstep j => ?_⟩
    induction j using Fin.induction with
    | zero => exact h0
    | succ i hi =>
      have := hstep _ hi
      rwa [rot_apply, Fin.coeSucc_eq_succ] at this

/-- reversing the oriented line changes the sign of `cross` -/
theorem cross_swap (a b y : ℝ × ℝ) : cross b a y = -cross a b y := by
  unfold cross; ring

/-- a point of the segment `a b` other than `a` and `b` is `pt a b t` with `0 < t < 1` -/
theorem mem_segment_pt {a b x : ℝ × ℝ} (hx : x ∈ segment ℝ a b) (ha : x ≠ a) (hb : x ≠ b) :
    ∃ t ∈ Ioo (0 : ℝ) 1, pt a b t = x := by
  rw [segment_eq_pt] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
  · rintro rfl; exact ha (pt_zero a b)
  · rintro rfl; exact hb (pt_one a b)

/-- **The region bounded by a simple closed polygon has an oriented polygonal boundary**: it lies
on the left of all sides `v k → v (k+1)` (counter-clockwise polygon), or on the left of all
reversed sides `v (k+1) → v k` (clockwise polygon). -/
theorem region_orientedBoundary (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    OrientedBoundary (region v) v (fun k => v (k + 1)) ∨
      OrientedBoundary (region v) (fun k => v (k + 1)) v := by
  have hs := hv.simple
  rw [region_eq]
  rcases region_side hs with h | h
  · left
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply region_off
      simpa only [rot_apply] using hx
    · intro k x hx hxa hxb _
      obtain ⟨t, ht, rfl⟩ := mem_segment_pt hx hxa hxb
      have := h k t ht
      simpa only [rot_apply] using this
    · intro j k hjk
      have := hs.inter_finite hjk
      simpa only [rot_apply] using this
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply region_off
      intro i
      rw [rot_apply, segment_symm]
      exact hx i
    · intro k x hx hxa hxb _
      rw [segment_symm] at hx
      obtain ⟨t, ht, rfl⟩ := mem_segment_pt hx hxb hxa
      have := h k t ht
      simp only [rot_apply] at this
      filter_upwards [this] with y hy
      rw [cross_swap]
      exact ⟨fun hc => hy.2 (by linarith), fun hc => hy.1 (by linarith)⟩
    · intro j k hjk
      have := hs.inter_finite hjk
      simp only [rot_apply] at this
      rw [segment_symm ℝ (v (j + 1)), segment_symm ℝ (v (k + 1))]
      exact this

/-- **Orientation test.**  If the polygon turns left at a lexicographically smallest vertex
`v (i+1)`, the region lies on the left of all sides `v k → v (k+1)`. -/
theorem region_orientedBoundary_of_turn (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    (i : Fin (m + 3))
    (hmin : ∀ j, (v (i + 1)).1 ≤ (v j).1 ∧ ((v (i + 1)).1 = (v j).1 → (v (i + 1)).2 ≤ (v j).2))
    (hturn : 0 < cross (v i) (v (i + 1)) (v (i + 1 + 1))) :
    OrientedBoundary (region v) v (fun k => v (k + 1)) := by
  have hs := hv.simple
  rw [region_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply region_off
    simpa only [rot_apply] using hx
  · intro k x hx hxa hxb _
    obtain ⟨t, ht, rfl⟩ := mem_segment_pt hx hxa hxb
    have := region_left_of_turn hs i (by simpa only [rot_apply] using hmin)
      (by simpa only [rot_apply] using hturn) k ht
    simpa only [rot_apply] using this
  · intro j k hjk
    have := hs.inter_finite hjk
    simpa only [rot_apply] using this

end

end Stein.Polygon
