/-
Mathathon Round 1, Problem 67: official Lean statement, prepared by AI. It may contain errors.

Source (dhyan-aranha/Monsky, Apache License 2.0):
  https://github.com/dhyan-aranha/Monsky/blob/355f153f9007dbbbd0c2eed127dc194a5c1ef10f/Monsky/main_statement.lean
  https://github.com/dhyan-aranha/Monsky/blob/355f153f9007dbbbd0c2eed127dc194a5c1ef10f/Monsky/simplex_basic.lean
  https://github.com/dhyan-aranha/Monsky/blob/355f153f9007dbbbd0c2eed127dc194a5c1ef10f/Monsky/square.lean
Adapted: the statement of `Monsky` and the definitions it uses (`v`, `closed_simplex`,
`open_simplex`, `closed_hull`, `open_hull`, `unit_square`) are copied unchanged into
one file, inside `namespace Mathathon.P67`; the proof is replaced by `sorry`. Two changes for
Mathlib v4.35.0, where `EuclideanSpace` is no longer a function type and `Finset.toSet`
no longer exists: `v x y` is written `!₂[x, y]`, and `S.toSet` is written `(S : Set Triangle)`.
-/

import Mathlib
import Stein.Main

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²

open Classical
open BigOperators

namespace Mathathon.P67

-- Shorthand for defining an element of ℝ²
def v (x y : ℝ) : ℝ² := !₂[x, y]

-- Definition of an n-dimensional standard simplex.
def closed_simplex (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
def open_simplex   (n : ℕ)  : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

def closed_hull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closed_simplex n
def open_hull   {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' open_simplex n

def unit_square : Fin 4 → ℝ² := (fun | 0 => v 0 0 | 1 => v 1 0 | 2 => v 1 1 | 3 => v 0 1)

/-!
## Proof

The official statement above is proved from the team's theorem `Stein.monsky` (Monsky's theorem
for dissections of `Set.Icc (0 : ℝ × ℝ) 1` into convex hulls of three non-collinear points).

* `toProd` is the coordinate map `ℝ² → ℝ × ℝ`; it is a linear homeomorphism and preserves
  Lebesgue measure (`volume_image_toProd`).
* `closed_hull f` is the convex hull of the points `f i` (`closed_hull_eq_convexHull`); for an
  affinely independent triangle the interior of `closed_hull Δ` lies in `open_hull Δ`
  (`interior_closed_hull_subset`); `open_hull Δ` and `closed_hull Δ` always have the same area
  (`volume_open_hull`), given by the determinant formula `volume_closed_hull`.
* `even_card_of_dissection` is the direction "a dissection exists ⟹ `n ≠ 0` and `n` is even".
* For the converse, `stripTri` cuts the square into `k` vertical strips and each strip into two
  triangles along a diagonal; `dissection k` is the resulting set of `2 k` triangles.
-/

section Auxiliary

open MeasureTheory Set

/-! ### The coordinate map `ℝ² → ℝ × ℝ` -/

/-- The coordinate map `x ↦ (x 0, x 1)` from `ℝ²` to `ℝ × ℝ`, as a continuous linear
equivalence. -/
private noncomputable def toProd : ℝ² ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

private lemma toProd_apply (x : ℝ²) : toProd x = (x 0, x 1) := rfl

/-- The coordinate map preserves Lebesgue measure. -/
private lemma volume_image_toProd (A : Set ℝ²) : volume (toProd '' A) = volume A := by
  let e : ℝ² ≃ᵐ ℝ × ℝ := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)
  have hA : toProd '' A = e.symm ⁻¹' A := e.image_eq_preimage_symm A
  rw [hA, (he.symm e).measure_preimage_equiv]

/-! ### Hulls -/

private lemma open_hull_subset_closed_hull {n : ℕ} (f : Fin n → ℝ²) :
    open_hull f ⊆ closed_hull f :=
  image_mono fun _ h => ⟨fun i => (h.1 i).le, h.2⟩

/-- `closed_hull f` is the convex hull of the points `f i`. -/
private lemma closed_hull_eq_convexHull {n : ℕ} (f : Fin n → ℝ²) :
    closed_hull f = convexHull ℝ (range f) := by
  apply Subset.antisymm
  · rintro _ ⟨α, hα, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hα.1 i) hα.2
      fun i _ => subset_convexHull ℝ _ (mem_range_self i)
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ⟨fun j => ?_, by simp⟩, by simp⟩
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ s t hs ht hst
      refine ⟨fun i => s * α i + t * β i,
        ⟨fun i => add_nonneg (mul_nonneg hs (hα.1 i)) (mul_nonneg ht (hβ.1 i)), ?_⟩, ?_⟩
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hα.2, hβ.2, mul_one,
          mul_one, hst]
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

private lemma range_triangle (Δ : Triangle) : range Δ = {Δ 0, Δ 1, Δ 2} := by
  ext x
  simp [Fin.exists_fin_succ, eq_comm]

/-- The interior of a non-degenerate closed triangle is contained in the open triangle. -/
private lemma interior_closed_hull_subset {Δ : Triangle} (hΔ : AffineIndependent ℝ Δ) :
    interior (closed_hull Δ) ⊆ open_hull Δ := by
  have htop : affineSpan ℝ (range Δ) = ⊤ :=
    hΔ.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simp)
  let b : AffineBasis (Fin 3) ℝ ℝ² := ⟨Δ, hΔ, htop⟩
  intro x hx
  rw [closed_hull_eq_convexHull, show range Δ = range b from rfl, b.interior_convexHull] at hx
  exact ⟨fun i => b.coord i x, ⟨hx, b.sum_coord_apply_eq_one x⟩,
    b.linear_combination_coord_eq_self x⟩

/-- A degenerate closed triangle is a null set. -/
private lemma volume_closed_hull_eq_zero {Δ : Triangle} (hΔ : ¬AffineIndependent ℝ Δ) :
    volume (closed_hull Δ) = 0 := by
  have hcol : Collinear ℝ {Δ 0, Δ 1, Δ 2} := by
    by_contra h
    apply hΔ
    convert affineIndependent_iff_not_collinear_set.2 h using 1
    funext i
    fin_cases i <;> rfl
  have hne : affineSpan ℝ {Δ 0, Δ 1, Δ 2} ≠ ⊤ := by
    intro htop
    have h1 := collinear_iff_finrank_le_one.1 hcol
    rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top] at h1
    simp at h1
  have hsub : closed_hull Δ ⊆ affineSpan ℝ {Δ 0, Δ 1, Δ 2} := by
    rw [closed_hull_eq_convexHull, range_triangle]
    exact convexHull_subset_affineSpan _
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume _ hne)

/-- The open and the closed triangle have the same area. -/
private lemma volume_open_hull (Δ : Triangle) :
    volume (open_hull Δ) = volume (closed_hull Δ) := by
  by_cases hΔ : AffineIndependent ℝ Δ
  · refine le_antisymm (measure_mono (open_hull_subset_closed_hull Δ)) ?_
    have hconv : Convex ℝ (closed_hull Δ) := by
      rw [closed_hull_eq_convexHull]
      exact convex_convexHull ℝ _
    have hsub : closed_hull Δ ⊆ open_hull Δ ∪ frontier (closed_hull Δ) := fun x hx => by
      by_cases hxi : x ∈ interior (closed_hull Δ)
      · exact Or.inl (interior_closed_hull_subset hΔ hxi)
      · exact Or.inr ⟨subset_closure hx, hxi⟩
    calc volume (closed_hull Δ) ≤ volume (open_hull Δ ∪ frontier (closed_hull Δ)) :=
          measure_mono hsub
      _ ≤ volume (open_hull Δ) + volume (frontier (closed_hull Δ)) := measure_union_le _ _
      _ = volume (open_hull Δ) := by rw [hconv.addHaar_frontier volume, add_zero]
  · have h0 := volume_closed_hull_eq_zero hΔ
    rw [h0]
    exact measure_mono_null (open_hull_subset_closed_hull Δ) h0

/-- In coordinates, a closed triangle is the convex hull of its three vertices. -/
private lemma toProd_image_closed_hull (Δ : Triangle) :
    toProd '' closed_hull Δ = convexHull ℝ {toProd (Δ 0), toProd (Δ 1), toProd (Δ 2)} := by
  rw [closed_hull_eq_convexHull, range_triangle,
    show ⇑toProd = ⇑(toProd : ℝ² →ₗ[ℝ] ℝ × ℝ) from rfl, LinearMap.image_convexHull]
  simp [image_insert_eq]

/-- The area of a closed triangle, from the team's `Stein.volume_triangle`. -/
private lemma volume_closed_hull (Δ : Triangle) :
    volume (closed_hull Δ) = ENNReal.ofReal
      (|Stein.det (toProd (Δ 1) - toProd (Δ 0)) (toProd (Δ 2) - toProd (Δ 0))| / 2) := by
  rw [← volume_image_toProd, toProd_image_closed_hull, Stein.volume_triangle]

/-! ### The unit square -/

private lemma mem_closed_hull_unit_square (x : ℝ²) :
    x ∈ closed_hull unit_square ↔ (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := by
  constructor
  · rintro ⟨α, ⟨h0, h1⟩, rfl⟩
    have h0' := h0 0
    have h1' := h0 1
    have h2' := h0 2
    have h3' := h0 3
    rw [Fin.sum_univ_four] at h1
    simp only [Fin.sum_univ_four, unit_square, v, PiLp.add_apply, PiLp.smul_apply]
    simp
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨![(1 - x 0) * (1 - x 1), x 0 * (1 - x 1), x 0 * x 1, (1 - x 0) * x 1],
      ⟨fun i => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> simp <;> nlinarith
    · simp [Fin.sum_univ_four]
      ring
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_four, unit_square, v] <;> ring

/-- In coordinates, the unit square is `[0, 1]²`. -/
private lemma toProd_image_unit_square :
    toProd '' closed_hull unit_square = Icc (0 : ℝ × ℝ) 1 := by
  ext p
  rw [mem_Icc, Prod.le_def, Prod.le_def]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := (mem_closed_hull_unit_square x).1 hx
    simpa [toProd_apply, and_and_and_comm] using this
  · intro hp
    refine ⟨v p.1 p.2, (mem_closed_hull_unit_square _).2 ?_, rfl⟩
    simpa [v, and_and_and_comm] using hp

/-! ### A dissection exists only for even `n ≠ 0` -/

/-- If the unit square is dissected into the triangles of `S`, all of the same area, then `S`
is non-empty and has an even number of elements.  This is the team's theorem `Stein.monsky`,
transported along the coordinate map `toProd`. -/
private lemma even_card_of_dissection (S : Finset Triangle)
    (hcover : closed_hull unit_square = ⋃ Δ ∈ S, closed_hull Δ)
    (hdisj : Set.PairwiseDisjoint (S : Set Triangle) open_hull)
    (hvol : ∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, volume (open_hull Δ₁) = volume (open_hull Δ₂)) :
    S.card ≠ 0 ∧ Even S.card := by
  -- the square has positive area, so one of the triangles has positive area
  have hsq : volume (closed_hull unit_square) ≠ 0 := by
    rw [← volume_image_toProd, toProd_image_unit_square, Icc_prod_eq,
      Measure.volume_eq_prod, Measure.prod_prod]
    simp
  obtain ⟨Δ₀, hΔ₀, h₀⟩ : ∃ Δ ∈ S, volume (closed_hull Δ) ≠ 0 := by
    by_contra h
    apply hsq
    rw [hcover]
    exact (measure_biUnion_null_iff S.countable_toSet).2
      fun Δ hΔ => by_contra fun hne => h ⟨Δ, hΔ, hne⟩
  -- hence all triangles have positive area and are non-degenerate
  have hpos : ∀ Δ ∈ S, volume (open_hull Δ) ≠ 0 := fun Δ hΔ => by
    rw [hvol Δ hΔ Δ₀ hΔ₀, volume_open_hull]
    exact h₀
  have hind : ∀ Δ ∈ S, AffineIndependent ℝ Δ := fun Δ hΔ => by
    by_contra h
    exact hpos Δ hΔ (by rw [volume_open_hull]; exact volume_closed_hull_eq_zero h)
  refine ⟨Finset.card_ne_zero.2 ⟨Δ₀, hΔ₀⟩, ?_⟩
  -- the images of the closed triangles form a dissection of `[0, 1]²` in the team's sense
  have key := Stein.monsky (fun Δ : S => toProd '' closed_hull Δ.1) ?_ ?_
  · rwa [Fintype.card_coe] at key
  · refine ⟨fun Δ => ?_, fun Δ₁ Δ₂ hne => ?_, ?_⟩
    · refine ⟨_, _, _, ?_, toProd_image_closed_hull Δ.1⟩
      rw [← affineIndependent_iff_not_collinear_set]
      convert (hind Δ.1 Δ.2).map' toProd.toAffineEquiv.toAffineMap toProd.injective using 1
      funext i
      fin_cases i <;> rfl
    · have h1 : ∀ Δ : S, interior (toProd '' closed_hull Δ.1) ⊆ toProd '' open_hull Δ.1 :=
        fun Δ => by
          rw [← show toProd '' interior (closed_hull Δ.1) = interior (toProd '' closed_hull Δ.1)
            from toProd.toHomeomorph.image_interior _]
          exact image_mono (interior_closed_hull_subset (hind Δ.1 Δ.2))
      refine Disjoint.mono (h1 _) (h1 _) ?_
      exact (disjoint_image_iff toProd.injective).2
        (hdisj Δ₁.2 Δ₂.2 fun h => hne (Subtype.ext h))
    · rw [← image_iUnion, ← toProd_image_unit_square, hcover]
      congr 1
      ext x
      simp
  · intro Δ₁ Δ₂
    simp only [volume_image_toProd, ← volume_open_hull]
    exact hvol _ Δ₁.2 _ Δ₂.2

/-! ### An explicit dissection into `2 k` triangles -/

/-- The two triangles into which a diagonal cuts the strip `[j / k, (j + 1) / k] × [0, 1]`:
the lower right one for `false`, the upper left one for `true`. -/
private noncomputable def stripTri (k j : ℝ) : Bool → Triangle
  | false => ![v (j / k) 0, v ((j + 1) / k) 0, v ((j + 1) / k) 1]
  | true => ![v ((j + 1) / k) 1, v (j / k) 1, v (j / k) 0]

/-- The barycentric coordinates of `x` with respect to `stripTri k j b`. -/
private noncomputable def bary (k j : ℝ) (b : Bool) (x : ℝ²) : Fin 3 → ℝ :=
  match b with
  | false => ![1 - (k * x 0 - j), k * x 0 - j - x 1, x 1]
  | true => ![k * x 0 - j, x 1 - (k * x 0 - j), 1 - x 1]

/-- `x` is the combination of the vertices of `stripTri k j b` with weights `α` of sum `1` if and
only if `α` are the barycentric coordinates of `x`. -/
private lemma stripTri_combination {k : ℝ} (hk : k ≠ 0) (j : ℝ) (b : Bool) (α : Fin 3 → ℝ)
    (x : ℝ²) : (∑ i, α i = 1 ∧ ∑ i, α i • stripTri k j b i = x) ↔ α = bary k j b x := by
  constructor
  · rintro ⟨h1, rfl⟩
    rw [Fin.sum_univ_three] at h1
    have h0 : α 0 = 1 - α 1 - α 2 := by linarith
    funext i
    cases b <;> fin_cases i <;>
      simp [bary, stripTri, v, Fin.sum_univ_three, h0] <;> field_simp <;> ring
  · rintro rfl
    constructor
    · cases b <;> simp [bary, Fin.sum_univ_three]
    · ext i
      cases b <;> fin_cases i <;>
        simp [bary, stripTri, v, Fin.sum_univ_three] <;> field_simp <;> ring

private lemma mem_closed_hull_stripTri {k : ℝ} (hk : k ≠ 0) (j : ℝ) (b : Bool) (x : ℝ²) :
    x ∈ closed_hull (stripTri k j b) ↔ ∀ i, 0 ≤ bary k j b x i := by
  constructor
  · rintro ⟨α, ⟨h0, h1⟩, hx⟩
    rw [← (stripTri_combination hk j b α x).1 ⟨h1, hx⟩]
    exact h0
  · intro h
    have h' := (stripTri_combination hk j b _ x).2 rfl
    exact ⟨_, ⟨h, h'.1⟩, h'.2⟩

private lemma mem_open_hull_stripTri {k : ℝ} (hk : k ≠ 0) (j : ℝ) (b : Bool) (x : ℝ²) :
    x ∈ open_hull (stripTri k j b) ↔ ∀ i, 0 < bary k j b x i := by
  constructor
  · rintro ⟨α, ⟨h0, h1⟩, hx⟩
    rw [← (stripTri_combination hk j b α x).1 ⟨h1, hx⟩]
    exact h0
  · intro h
    have h' := (stripTri_combination hk j b _ x).2 rfl
    exact ⟨_, ⟨h, h'.1⟩, h'.2⟩

/-- Each of the triangles `stripTri k j b` has area `1 / (2 k)`. -/
private lemma volume_open_hull_stripTri {k : ℝ} (hk : 0 < k) (j : ℝ) (b : Bool) :
    volume (open_hull (stripTri k j b)) = ENNReal.ofReal (1 / (2 * k)) := by
  have h : (j + 1) / k - j / k = 1 / k := by ring
  rw [volume_open_hull, volume_closed_hull]
  congr 1
  cases b <;> simp [stripTri, toProd_apply, v, Stein.det, h, abs_of_pos hk] <;> ring

/-- The dissection of the unit square into `2 k` triangles: `k` vertical strips, each cut into
two triangles by a diagonal. -/
private noncomputable def dissection (k : ℕ) : Finset Triangle :=
  Finset.univ.image fun p : Fin k × Bool => stripTri k p.1 p.2

private lemma disjoint_open_hull_stripTri {k : ℕ} (hk : k ≠ 0) {p q : Fin k × Bool}
    (hpq : p ≠ q) :
    Disjoint (open_hull (stripTri k p.1 p.2)) (open_hull (stripTri k q.1 q.2)) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  refine Set.disjoint_left.2 fun x hp hq => hpq ?_
  rw [mem_open_hull_stripTri hk'] at hp hq
  obtain ⟨⟨i, hi⟩, b⟩ := p
  obtain ⟨⟨j, hj⟩, c⟩ := q
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hq0 := hq 0
  have hq1 := hq 1
  have hq2 := hq 2
  have hij : i = j := by
    have h1 : (i : ℝ) < j + 1 := by
      cases b <;> cases c <;> simp [bary] at hp0 hp1 hp2 hq0 hq1 hq2 <;> linarith
    have h2 : (j : ℝ) < i + 1 := by
      cases b <;> cases c <;> simp [bary] at hp0 hp1 hp2 hq0 hq1 hq2 <;> linarith
    have h1' : i < j + 1 := by exact_mod_cast h1
    have h2' : j < i + 1 := by exact_mod_cast h2
    omega
  subst hij
  have hbc : b = c := by
    cases b <;> cases c <;> simp [bary] at hp0 hp1 hp2 hq0 hq1 hq2 ⊢ <;> linarith
  rw [hbc]

private lemma stripTri_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective fun p : Fin k × Bool => stripTri k p.1 p.2 := by
  intro p q hpq
  by_contra hne
  have hd := disjoint_open_hull_stripTri hk hne
  simp only at hpq
  rw [hpq, disjoint_self, Set.bot_eq_empty] at hd
  have hv := volume_open_hull_stripTri (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) q.1 q.2
  rw [hd, measure_empty] at hv
  have : (0 : ℝ) < 1 / (2 * k) := by positivity
  exact (ENNReal.ofReal_pos.2 this).ne hv

private lemma card_dissection {k : ℕ} (hk : k ≠ 0) : (dissection k).card = k + k := by
  rw [dissection, Finset.card_image_of_injective _ (stripTri_injective hk)]
  simp
  ring

private lemma closed_hull_unit_square_eq_iUnion {k : ℕ} (hk : k ≠ 0) :
    closed_hull unit_square = ⋃ Δ ∈ dissection k, closed_hull Δ := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  ext x
  rw [dissection, Finset.set_biUnion_finset_image]
  simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_closed_hull_unit_square,
    mem_closed_hull_stripTri hk0.ne']
  constructor
  · rintro ⟨⟨hx0, hx1⟩, hy0, hy1⟩
    -- the strip containing `x`
    obtain ⟨j, hj0, hj1⟩ : ∃ j : Fin k, 0 ≤ k * x 0 - j ∧ k * x 0 - j ≤ 1 := by
      have hkx : 0 ≤ k * x 0 := mul_nonneg hk0.le hx0
      by_cases hm : ⌊k * x 0⌋₊ < k
      · exact ⟨⟨_, hm⟩, by have := Nat.floor_le hkx; simp only; linarith,
          by have := Nat.lt_floor_add_one (k * x 0); simp only; linarith⟩
      · have h1 : (k : ℝ) ≤ ⌊k * x 0⌋₊ := by exact_mod_cast not_lt.1 hm
        have h2 := Nat.floor_le hkx
        have h3 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
          rw [Nat.cast_sub (Nat.pos_of_ne_zero hk), Nat.cast_one]
        have h4 : k * x 0 ≤ k * 1 := mul_le_mul_of_nonneg_left hx1 hk0.le
        exact ⟨⟨k - 1, by omega⟩, by simp only [h3]; linarith, by simp only [h3]; linarith⟩
    by_cases h : k * x 0 - j ≤ x 1
    · refine ⟨(j, true), fun i => ?_⟩
      fin_cases i <;> simp [bary] <;> linarith
    · refine ⟨(j, false), fun i => ?_⟩
      fin_cases i <;> simp [bary] <;> linarith
  · rintro ⟨⟨j, b⟩, h⟩
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have hj : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    have hx0 : k * 0 ≤ k * x 0 := by
      cases b <;> simp [bary] at h0 h1 h2 ⊢ <;> nlinarith
    have hx1 : k * x 0 ≤ k * 1 := by
      cases b <;> simp [bary] at h0 h1 h2 ⊢ <;> nlinarith
    refine ⟨⟨le_of_mul_le_mul_left hx0 hk0, le_of_mul_le_mul_left hx1 hk0⟩, ?_, ?_⟩ <;>
      cases b <;> simp [bary] at h0 h1 h2 <;> linarith

end Auxiliary

theorem Monsky (n : ℕ):
    (∃ (S : Finset Triangle),
      closed_hull unit_square = ⋃ (Δ ∈ S), closed_hull Δ ∧
      Set.PairwiseDisjoint (S : Set Triangle) open_hull ∧
      (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, MeasureTheory.volume (open_hull Δ₁) = MeasureTheory.volume (open_hull Δ₂)) ∧
      S.card = n)
    ↔ (n ≠ 0 ∧ Even n) := by
  constructor
  · rintro ⟨S, hcover, hdisj, hvol, rfl⟩
    exact even_card_of_dissection S hcover hdisj hvol
  · rintro ⟨hn, k, rfl⟩
    have hk : k ≠ 0 := by
      rintro rfl
      exact hn rfl
    refine ⟨dissection k, closed_hull_unit_square_eq_iUnion hk, ?_, ?_, card_dissection hk⟩
    · intro Δ₁ h₁ Δ₂ h₂ hne
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h₁
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 h₂
      exact disjoint_open_hull_stripTri hk fun h => hne (by rw [h])
    · intro Δ₁ h₁ Δ₂ h₂
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h₁
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 h₂
      have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
      rw [volume_open_hull_stripTri hk0, volume_open_hull_stripTri hk0]

end Mathathon.P67
