import Stein.Geometry.Dissection

/-!
# The unit square

* `Stein.convex_boundary` : a set cut out by finitely many closed half-planes lies on the left of
  its oriented boundary (`Stein.OrientedBoundary`), under natural conditions on the sides;
* `Stein.square_boundary` : the unit square `[0,1]² = Set.Icc (0 : ℝ × ℝ) 1` lies on the left of
  its four counter-clockwise sides `Stein.sqA k → Stein.sqB k`;
* `Stein.square_special` : these four sides form a special boundary (`Stein.Special`).

Together with `Stein.stein_conjecture_of_orientedBoundary` this gives Monsky's theorem
(`Stein.monsky` in `Stein/Main.lean`) without using the polygon part (`Stein/Polygon/`).
-/

open Set Filter Topology

namespace Stein

noncomputable section

/-- **Convex polygons.**  If `S` is the intersection of the closed half-planes on the left of the
oriented sides `A k → B k`, every side lies in `S`, every point of `S` on the line of a side lies
on that side, and two different sides have finitely many common points, then `S` lies on the left
of its oriented boundary `A k → B k`. -/
theorem convex_boundary {κ : Type*} [Finite κ] (A B : κ → ℝ × ℝ) (S : Set (ℝ × ℝ))
    (hSdef : ∀ x, x ∈ S ↔ ∀ k, 0 ≤ cross (A k) (B k) x)
    (hin : ∀ k, segment ℝ (A k) (B k) ⊆ S)
    (hedge : ∀ k x, x ∈ S → cross (A k) (B k) x = 0 → x ∈ segment ℝ (A k) (B k))
    (hfin : ∀ j k, j ≠ k → (segment ℝ (A j) (B j) ∩ segment ℝ (A k) (B k)).Finite) :
    OrientedBoundary S A B := by
  refine ⟨?_, ?_, hfin⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · left
      have hpos : ∀ k, 0 < cross (A k) (B k) x := fun k =>
        lt_of_le_of_ne ((hSdef x).1 hxS k) (fun h => hx k (hedge k x hxS h.symm))
      have hev : ∀ k, ∀ᶠ y in 𝓝 x, 0 < cross (A k) (B k) y := fun k =>
        ((cross_continuous (A k) (B k)).tendsto x).eventually (lt_mem_nhds (hpos k))
      filter_upwards [eventually_all.2 hev] with y hy
      exact (hSdef y).2 (fun k => (hy k).le)
    · right
      have hex : ∃ k, cross (A k) (B k) x < 0 := by
        by_contra hno
        exact hxS ((hSdef x).2 (fun k => not_lt.1 (fun h => hno ⟨k, h⟩)))
      obtain ⟨k, hk⟩ := hex
      filter_upwards [((cross_continuous (A k) (B k)).tendsto x).eventually (gt_mem_nhds hk)]
        with y hy hyS
      exact absurd ((hSdef y).1 hyS k) (not_le.2 hy)
  · intro k x hxk _ _ huniq
    have hxS : x ∈ S := hin k hxk
    have hev : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ k → 0 < cross (A j) (B j) y := by
      intro j
      by_cases hjk : j = k
      · exact Eventually.of_forall (fun y h => absurd hjk h)
      · have hpos : 0 < cross (A j) (B j) x :=
          lt_of_le_of_ne ((hSdef x).1 hxS j) (fun h => huniq j hjk (hedge j x hxS h.symm))
        exact (((cross_continuous (A j) (B j)).tendsto x).eventually (lt_mem_nhds hpos)).mono
          (fun y hy _ => hy)
    filter_upwards [eventually_all.2 hev] with y hy
    constructor
    · intro hpos
      apply (hSdef y).2
      intro j
      by_cases hjk : j = k
      · rw [hjk]; exact hpos.le
      · exact (hy j hjk).le
    · intro hneg hyS
      exact absurd ((hSdef y).1 hyS k) (not_le.2 hneg)

/-- `cross a b` vanishes on the segment from `a` to `b`. -/
private theorem cross_eq_zero_of_mem_segment {a b x : ℝ × ℝ} (hx : x ∈ segment ℝ a b) :
    cross a b x = 0 := by
  obtain ⟨s, t, _, _, hst, rfl⟩ := hx
  rw [cross_comb _ _ _ _ _ _ hst]
  simp only [cross]
  ring

/-- The starting points of the four sides of the unit square, counter-clockwise. -/
def sqA : Fin 4 → ℝ × ℝ := ![(0, 0), (1, 0), (1, 1), (0, 1)]

/-- The end points of the four sides of the unit square, counter-clockwise. -/
def sqB : Fin 4 → ℝ × ℝ := ![(1, 0), (1, 1), (0, 1), (0, 0)]

/-- The functions `cross` of the four sides of the unit square. -/
private theorem sq_cross (x : ℝ × ℝ) :
    cross (sqA 0) (sqB 0) x = x.2 ∧ cross (sqA 1) (sqB 1) x = 1 - x.1 ∧
      cross (sqA 2) (sqB 2) x = 1 - x.2 ∧ cross (sqA 3) (sqB 3) x = x.1 := by
  simp [sqA, sqB, cross]

/-- Membership in the unit square, in coordinates. -/
private theorem mem_square (x : ℝ × ℝ) :
    x ∈ Set.Icc (0 : ℝ × ℝ) 1 ↔ (0 ≤ x.1 ∧ x.1 ≤ 1) ∧ (0 ≤ x.2 ∧ x.2 ≤ 1) := by
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
  tauto

/-- The unit square lies on the left of its four counter-clockwise sides. -/
theorem square_boundary : OrientedBoundary (Set.Icc (0 : ℝ × ℝ) 1) sqA sqB := by
  have hSdef : ∀ x : ℝ × ℝ, x ∈ Set.Icc (0 : ℝ × ℝ) 1 ↔ ∀ k, 0 ≤ cross (sqA k) (sqB k) x := by
    intro x
    obtain ⟨c0, c1, c2, c3⟩ := sq_cross x
    rw [mem_square, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
      Fin.forall_fin_succ]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
    have e3 : (Fin.succ 2 : Fin 4) = 3 := rfl
    rw [e3, c0, c1, c2, c3]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, by linarith, by linarith, h1⟩
    · rintro ⟨h3, h2, h4, h1⟩
      exact ⟨⟨h1, by linarith⟩, h3, by linarith⟩
  have hin : ∀ k, segment ℝ (sqA k) (sqB k) ⊆ Set.Icc (0 : ℝ × ℝ) 1 := by
    intro k
    apply (convex_Icc (0 : ℝ × ℝ) 1).segment_subset <;>
      (rw [mem_square]; fin_cases k <;> simp [sqA, sqB])
  apply convex_boundary sqA sqB _ hSdef hin
  · intro k x hx h0
    rw [mem_square] at hx
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
    obtain ⟨c0, c1, c2, c3⟩ := sq_cross x
    fin_cases k
    · have h0' : x.2 = 0 := by rw [← c0]; exact h0
      exact ⟨1 - x.1, x.1, by linarith, h1, by ring, by
        ext <;> simp [sqA, sqB, h0']⟩
    · have h0' : x.1 = 1 := by
        have : 1 - x.1 = 0 := by rw [← c1]; exact h0
        linarith
      exact ⟨1 - x.2, x.2, by linarith, h3, by ring, by
        ext <;> simp [sqA, sqB, h0']⟩
    · have h0' : x.2 = 1 := by
        have : 1 - x.2 = 0 := by rw [← c2]; exact h0
        linarith
      exact ⟨x.1, 1 - x.1, h1, by linarith, by ring, by
        ext <;> simp [sqA, sqB, h0']⟩
    · have h0' : x.1 = 0 := by rw [← c3]; exact h0
      exact ⟨x.2, 1 - x.2, h3, by linarith, by ring, by
        ext <;> simp [sqA, sqB, h0']⟩
  · intro j k hjk
    apply Set.Subsingleton.finite
    rintro x ⟨hxj, hxk⟩ y ⟨hyj, hyk⟩
    have e1 := cross_eq_zero_of_mem_segment hxj
    have e2 := cross_eq_zero_of_mem_segment hxk
    have e3 := cross_eq_zero_of_mem_segment hyj
    have e4 := cross_eq_zero_of_mem_segment hyk
    obtain ⟨cx0, cx1, cx2, cx3⟩ := sq_cross x
    obtain ⟨cy0, cy1, cy2, cy3⟩ := sq_cross y
    fin_cases j <;> fin_cases k <;>
      first
        | exact absurd rfl hjk
        | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at e1 e2 e3 e4
           exact Prod.ext (by linarith) (by linarith))

/-- The boundary of the unit square is special. -/
theorem square_special : Special sqA sqB := by
  intro d _
  rw [Fin.sum_univ_four]
  have e0 : sqB 0 - sqA 0 = (1, 0) := by ext <;> simp [sqA, sqB]
  have e1 : sqB 1 - sqA 1 = (0, 1) := by ext <;> simp [sqA, sqB]
  have e2 : sqB 2 - sqA 2 = -(1, 0) := by ext <;> simp [sqA, sqB]
  have e3 : sqB 3 - sqA 3 = -(0, 1) := by ext <;> simp [sqA, sqB]
  rw [e0, e1, e2, e3, par_neg, par_neg]
  abel

end

end Stein
