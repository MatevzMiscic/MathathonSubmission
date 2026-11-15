import Stein.Polygon.Frontier

/-!
# Convex polygons and the unit square

* `windingNumber_pos_of_left` : a point strictly on the left of all sides has positive winding
  number.
* `windingNumber_eq_zero_of_notMem_convexHull`, `region_subset_convexHull` : the winding number
  vanishes outside the convex hull of the vertices, so the region is contained in it.
* `region_eq_convexHull` : for a strictly convex polygon given counter-clockwise,
  `region v = convexHull ℝ (range v)`.
* `simplePolygon_of_convex` : such a polygon is a simple closed polygon.
* `unitSquare`, `region_unitSquare`, `simplePolygon_unitSquare` : the unit square as a polygon
  with four vertices; its region is `Set.Icc 0 1`.

These statements are not used in the proof of the main theorem; they show that the definitions
`SimplePolygon` and `region` of `Stein/Polygon/Region.lean` give the expected result for convex
polygons, in particular for the unit square.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- `a` lies on the line `a b`. -/
theorem cross_self_left (a b : ℝ × ℝ) : cross a b a = 0 := by simp [cross]

/-- a point strictly on the left of all sides has positive winding number -/
theorem wind_pos_of_left [Nonempty ι] {x : ℝ × ℝ} (h : ∀ i, 0 < cross (v i) (v (σ i)) x) :
    0 < wind v σ x := by
  have hxv : ∀ i, x ≠ v i := by
    intro i hi
    have := h i
    rw [hi, cross_self_left] at this
    exact lt_irrefl _ this
  have hpos : ∀ i, 0 < ang (v i) (v (σ i)) x := by
    intro i
    have him := zq_im_pos (b := v (σ i)) (hxv i) (h i)
    apply lt_of_le_of_ne (arg_nonneg_iff.2 him.le)
    intro h0
    have := (arg_eq_zero_iff.1 h0.symm).2
    rw [this] at him
    exact lt_irrefl _ him
  have hsum : 0 < angSum v σ x := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  rw [angSum_eq v σ hxv] at hsum
  have h2 : (0 : ℝ) < wind v σ x := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    exact (mul_pos_iff_of_pos_left hpi).1 hsum
  exact_mod_cast h2

/-- the winding number vanishes outside the convex hull of the vertices -/
theorem wind_eq_zero_of_notMem_convexHull {x : ℝ × ℝ} (hx : x ∉ convexHull ℝ (range v)) :
    wind v σ x = 0 := by
  obtain ⟨f, u, hfx, hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ (range v))
    ((finite_range v).isClosed_convexHull ℝ) hx
  have hlin : ∀ w : ℝ × ℝ, f w = w.1 * f (1, 0) + w.2 * f (0, 1) := by
    intro w
    have e : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
      apply Prod.ext <;> simp
    conv_lhs => rw [e]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  apply wind_eq_zero_of_dir σ ((f (1, 0) : ℂ) - (f (0, 1) : ℂ) * I)
  intro j
  have h1 := hf (v j) (subset_convexHull ℝ _ (mem_range_self j))
  have h2 : 0 < f (v j - x) := by rw [map_sub]; linarith
  rw [hlin] at h2
  have e : (((f (1, 0) : ℂ) - (f (0, 1) : ℂ) * I) * (toC (v j) - toC x)).re =
      (v j - x).1 * f (1, 0) + (v j - x).2 * f (0, 1) := by
    simp [toC]
    ring
  rw [e]
  exact h2

end cyc

variable {m : ℕ}

/-- a point strictly on the left of all sides `v k → v (k+1)` has positive winding number -/
theorem windingNumber_pos_of_left (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ}
    (h : ∀ k, 0 < cross (v k) (v (k + 1)) x) : 0 < windingNumber v x := by
  rw [windingNumber_eq]
  apply wind_pos_of_left
  intro i
  rw [rot_apply]
  exact h i

/-- the winding number vanishes outside the convex hull of the vertices -/
theorem windingNumber_eq_zero_of_notMem_convexHull (v : Fin (m + 3) → ℝ × ℝ) {x : ℝ × ℝ}
    (hx : x ∉ convexHull ℝ (range v)) : windingNumber v x = 0 := by
  rw [windingNumber_eq]
  exact wind_eq_zero_of_notMem_convexHull hx

/-- the region is contained in the convex hull of the vertices (any closed polygonal curve) -/
theorem region_subset_convexHull (v : Fin (m + 3) → ℝ × ℝ) :
    region v ⊆ convexHull ℝ (range v) := by
  rintro x (hx | hx)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (mem_range_self k))
      (subset_convexHull ℝ _ (mem_range_self (k + 1))) hk
  · by_contra hn
    exact hx (windingNumber_eq_zero_of_notMem_convexHull v hn)

/-- a closed side together with the open half-plane on its left is a convex set -/
theorem convex_side_union (a b : ℝ × ℝ) :
    Convex ℝ (segment ℝ a b ∪ {y | 0 < cross a b y}) := by
  have hc : ∀ (y y' : ℝ × ℝ) (s s' : ℝ), s + s' = 1 →
      cross a b (s • y + s' • y') =
        s * cross a b y + s' * cross a b y' := by
    intro y y' s s' h
    simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    linear_combination ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) * h
  have hz : ∀ y ∈ segment ℝ a b, cross a b y = 0 :=
    fun y hy => cross_of_mem_segment hy
  intro y hy y' hy' s s' hs hs' hss
  rcases hy with hy | hy <;> rcases hy' with hy' | hy'
  · exact Or.inl ((convex_segment a b) hy hy' hs hs' hss)
  · rcases hs'.lt_or_eq with h | h
    · right
      show 0 < cross a b (s • y + s' • y')
      rw [hc _ _ _ _ hss, hz y hy, mul_zero, zero_add]
      exact mul_pos h hy'
    · left
      have h1 : s = 1 := by linarith
      rw [← h, h1, one_smul, zero_smul, add_zero]
      exact hy
  · rcases hs.lt_or_eq with h | h
    · right
      show 0 < cross a b (s • y + s' • y')
      rw [hc _ _ _ _ hss, hz y' hy', mul_zero, add_zero]
      exact mul_pos h hy
    · left
      have h1 : s' = 1 := by linarith
      rw [← h, h1, one_smul, zero_smul, zero_add]
      exact hy'
  · right
    show 0 < cross a b (s • y + s' • y')
    rw [hc _ _ _ _ hss]
    have h1 : 0 < cross a b y := hy
    have h2 : 0 < cross a b y' := hy'
    rcases hs.lt_or_eq with h | h
    · have := mul_pos h h1
      have := mul_nonneg hs' h2.le
      linarith
    · have h3 : s' = 1 := by linarith
      rw [← h, h3]; linarith

/-- **Convex polygons.**  For a strictly convex polygon given counter-clockwise (every vertex
other than `v k`, `v (k+1)` lies strictly on the left of the side `v k → v (k+1)`), the region is
the convex hull of the vertices. -/
theorem region_eq_convexHull (v : Fin (m + 3) → ℝ × ℝ)
    (hconv : ∀ k j, j ≠ k → j ≠ k + 1 → 0 < cross (v k) (v (k + 1)) (v j)) :
    region v = convexHull ℝ (range v) := by
  apply Subset.antisymm (region_subset_convexHull v)
  intro x hx
  by_cases hb : x ∈ boundary v
  · exact Or.inl hb
  · right
    apply ne_of_gt
    apply windingNumber_pos_of_left
    intro k
    have hsub : convexHull ℝ (range v) ⊆
        segment ℝ (v k) (v (k + 1)) ∪ {y | 0 < cross (v k) (v (k + 1)) y} := by
      apply convexHull_min _ (convex_side_union _ _)
      rintro _ ⟨j, rfl⟩
      by_cases h1 : j = k
      · rw [h1]; exact Or.inl (left_mem_segment ℝ _ _)
      · by_cases h2 : j = k + 1
        · rw [h2]; exact Or.inl (right_mem_segment ℝ _ _)
        · exact Or.inr (hconv k j h1 h2)
    rcases hsub hx with h | h
    · exact absurd (mem_iUnion.2 ⟨k, h⟩) hb
    · exact h

/-- `k + 2 ≠ k` in `Fin (m + 3)`. -/
private theorem add_two_ne_self (k : Fin (m + 3)) : k + 1 + 1 ≠ k := by
  intro h
  have h2 : (1 + 1 : Fin (m + 3)) = 0 := by
    apply add_left_cancel (a := k); rw [← add_assoc, h, add_zero]
  have := congrArg Fin.val h2
  rw [Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- `cross a b` is affine along the line `c d`. -/
private theorem cross_pt_affine (a b c d : ℝ × ℝ) (t : ℝ) :
    cross a b (pt c d t) =
      (1 - t) * cross a b c + t * cross a b d := by
  simp only [cross, pt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

/-- **a strictly convex polygon given counter-clockwise is a simple closed polygon** -/
theorem simplePolygon_of_convex (v : Fin (m + 3) → ℝ × ℝ)
    (hconv : ∀ k j, j ≠ k → j ≠ k + 1 → 0 < cross (v k) (v (k + 1)) (v j)) :
    SimplePolygon v := by
  have hz : ∀ k, cross (v k) (v (k + 1)) (v k) = 0 ∧
      cross (v k) (v (k + 1)) (v (k + 1)) = 0 := fun k =>
    ⟨cross_of_mem_segment (left_mem_segment ℝ _ _), cross_of_mem_segment (right_mem_segment ℝ _ _)⟩
  have hnn : ∀ k j, 0 ≤ cross (v k) (v (k + 1)) (v j) := by
    intro k j
    by_cases h1 : j = k
    · rw [h1, (hz k).1]
    · by_cases h2 : j = k + 1
      · rw [h2, (hz k).2]
      · exact (hconv k j h1 h2).le
  have key : ∀ j k, k ≠ j → k ≠ j + 1 → ∀ x, x ∈ side v j → x ∈ side v k →
      j = k + 1 ∧ x = v j := by
    intro j k h1 h2 x hxj hxk
    have hc : cross (v j) (v (j + 1)) x = 0 := cross_of_mem_segment hxj
    unfold side at hxk
    rw [segment_eq_pt] at hxk
    obtain ⟨t, ht, rfl⟩ := hxk
    rw [cross_pt_affine] at hc
    have hpos := hconv j k h1 h2
    have hn := hnn j (k + 1)
    have ht1 : t = 1 := by
      by_contra hne
      have : 0 < 1 - t := by
        have := lt_of_le_of_ne ht.2 hne
        linarith
      have := mul_pos this hpos
      have := mul_nonneg ht.1 hn
      linarith
    rw [ht1] at hc ⊢
    rw [sub_self, zero_mul, zero_add, one_mul] at hc
    have hj : j = k + 1 := by
      by_contra hne
      by_cases h3 : k + 1 = j + 1
      · exact h1 (add_right_cancel h3)
      · exact absurd hc (hconv j (k + 1) (Ne.symm hne) h3).ne'
    exact ⟨hj, by rw [pt_one, hj]⟩
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_contra hne
    by_cases h1 : j = i + 1
    · have := hconv j i hne (by rw [h1]; exact (add_two_ne_self i).symm)
      rw [hij, (hz j).1] at this
      exact lt_irrefl _ this
    · have := hconv i j (Ne.symm hne) h1
      rw [← hij, (hz i).1] at this
      exact lt_irrefl _ this
  · intro j k hjk x hxj hxk
    by_cases h2 : k = j + 1
    · left
      have h3 : j ≠ k + 1 := by rw [h2]; exact (add_two_ne_self j).symm
      obtain ⟨e1, e2⟩ := key k j hjk h3 x hxk hxj
      exact ⟨e1, e2⟩
    · right
      exact key j k (Ne.symm hjk) h2 x hxj hxk

/-! ### The unit square -/

/-- the unit square as a polygon with four vertices, counter-clockwise -/
def unitSquare : Fin (1 + 3) → ℝ × ℝ := ![(0, 0), (1, 0), (1, 1), (0, 1)]

/-- The functions `cross` of the four sides of the unit square. -/
private theorem unitSquare_cross (x : ℝ × ℝ) :
    cross (unitSquare 0) (unitSquare (0 + 1)) x = x.2 ∧
    cross (unitSquare 1) (unitSquare (1 + 1)) x = 1 - x.1 ∧
    cross (unitSquare 2) (unitSquare (2 + 1)) x = 1 - x.2 ∧
    cross (unitSquare 3) (unitSquare (3 + 1)) x = x.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [unitSquare, cross]

/-- **The region of the unit square** (as a polygon with the four vertices `(0,0)`, `(1,0)`,
`(1,1)`, `(0,1)`) **is `[0,1]²`.** -/
theorem region_unitSquare : region unitSquare = Icc (0 : ℝ × ℝ) 1 := by
  apply Subset.antisymm
  · apply region_subset_Icc
    intro j
    fin_cases j <;> simp [unitSquare, Prod.le_def]
  · intro x hx
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
    simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one] at h1 h2 h3 h4
    obtain ⟨c0, c1, c2, c3⟩ := unitSquare_cross x
    have hside : ∀ k : Fin (1 + 3), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        x = pt (unitSquare k) (unitSquare (k + 1)) t → x ∈ region unitSquare := by
      intro k t h0 h1 e
      left
      refine mem_iUnion.2 ⟨k, ?_⟩
      rw [e]
      exact pt_mem_segment _ _ h0 h1
    by_cases e0 : x.2 = 0
    · apply hside 0 x.1 h1 h3
      apply Prod.ext <;> simp [unitSquare, pt, e0]
    by_cases e1 : x.1 = 1
    · apply hside 1 x.2 h2 h4
      apply Prod.ext <;> simp [unitSquare, pt, e1]
    by_cases e2 : x.2 = 1
    · apply hside 2 (1 - x.1) (by linarith) (by linarith)
      apply Prod.ext <;> simp [unitSquare, pt, e2]
    by_cases e3 : x.1 = 0
    · apply hside 3 (1 - x.2) (by linarith) (by linarith)
      apply Prod.ext <;> simp [unitSquare, pt, e3]
    right
    apply ne_of_gt
    apply windingNumber_pos_of_left
    intro k
    fin_cases k
    · show 0 < cross (unitSquare 0) (unitSquare (0 + 1)) x
      rw [c0]; exact lt_of_le_of_ne h2 (Ne.symm e0)
    · show 0 < cross (unitSquare 1) (unitSquare (1 + 1)) x
      rw [c1]; have := lt_of_le_of_ne h3 e1; linarith
    · show 0 < cross (unitSquare 2) (unitSquare (2 + 1)) x
      rw [c2]; have := lt_of_le_of_ne h4 e2; linarith
    · show 0 < cross (unitSquare 3) (unitSquare (3 + 1)) x
      rw [c3]; exact lt_of_le_of_ne h1 (Ne.symm e3)

/-- The unit square is strictly convex and given counter-clockwise. -/
theorem unitSquare_convex : ∀ k j : Fin (1 + 3), j ≠ k → j ≠ k + 1 →
    0 < cross (unitSquare k) (unitSquare (k + 1)) (unitSquare j) := by
  intro k j h1 h2
  fin_cases k <;> fin_cases j <;>
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | simp [unitSquare, cross]

/-- the unit square is a simple closed polygon -/
theorem simplePolygon_unitSquare : SimplePolygon unitSquare :=
  simplePolygon_of_convex unitSquare unitSquare_convex

/-- the convex hull of the vertices of the unit square is `[0,1]²` -/
theorem convexHull_unitSquare : convexHull ℝ (range unitSquare) = Icc (0 : ℝ × ℝ) 1 := by
  rw [← region_eq_convexHull unitSquare unitSquare_convex, region_unitSquare]

end

end Stein.Polygon
