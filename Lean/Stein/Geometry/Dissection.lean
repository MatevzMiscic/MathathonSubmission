import Stein.Algebra.Valuation
import Stein.Algebra.TheoremM
import Stein.Geometry.Balance

/-!
# The Main Theorem and Stein's conjecture, for regions lying on the left of their boundary

This file defines triangles (`Stein.IsTriangle`), triangles with vertices in `K²` for a subfield
`K` of `ℝ` (`Stein.IsTriangleOver`), dissections of a plane set into triangles
(`Stein.IsDissection`) and special boundaries (`Stein.Special`), and proves:

* `Stein.IsDissection.volume_eq_sum` : `Area S = Σ Area (T i)` (Lebesgue measure);
* `Stein.balanced_of_special` : Lemma 4.1, second sentence (special ⟹ balanced);
* `Stein.main_theorem_of_orientedBoundary` : Theorem 1.2 for a set `S` with
  `OrientedBoundary S A B`;
* `Stein.stein_conjecture_of_orientedBoundary` : Corollary 1.3 for such sets.

The versions for simple polygons given by their vertices, and Monsky's theorem, are in
`Stein/Main.lean`.
-/

open Set MeasureTheory

namespace Stein

noncomputable section

/-! ### Definitions -/

/-- A (closed, non-degenerate) triangle: the convex hull of three non-collinear points. -/
def IsTriangle (T : Set (ℝ × ℝ)) : Prop :=
  ∃ p q r : ℝ × ℝ, ¬Collinear ℝ {p, q, r} ∧ T = convexHull ℝ {p, q, r}

/-- The inclusion `K² → ℝ²` for a subfield `K` of `ℝ`. -/
def emb (K : Subfield ℝ) : K × K →+ ℝ × ℝ :=
  AddMonoidHom.prodMap (K.subtype : K →+ ℝ) (K.subtype : K →+ ℝ)

/-- A triangle whose vertices have their coordinates in the subfield `K ⊆ ℝ`. -/
def IsTriangleOver (K : Subfield ℝ) (T : Set (ℝ × ℝ)) : Prop :=
  ∃ p q r : K × K, ¬Collinear ℝ {emb K p, emb K q, emb K r} ∧
    T = convexHull ℝ {emb K p, emb K q, emb K r}

/-- A dissection of `S` into the triangles `T i`: each `T i` is a non-degenerate closed triangle,
different triangles have disjoint interiors, and the union of the triangles is `S`.
(T-junctions are allowed.) -/
structure IsDissection {ι : Type*} (S : Set (ℝ × ℝ)) (T : ι → Set (ℝ × ℝ)) : Prop where
  triangle : ∀ i, IsTriangle (T i)
  disjoint : ∀ i j, i ≠ j → Disjoint (interior (T i)) (interior (T j))
  union : (⋃ i, T i) = S

/-- **Special**: for every direction `d ≠ 0`, the boundary vectors `B k - A k` parallel to `d`
sum to `0`. -/
def Special {κ : Type*} [Fintype κ] (A B : κ → ℝ × ℝ) : Prop :=
  ∀ d : ℝ × ℝ, d ≠ 0 → ∑ k, par d (B k - A k) = 0

/-! ### Triangles: non-degeneracy, orientation, area -/

/-- Three non-collinear points `p, q, r` have `det (q - p, r - p) ≠ 0`. -/
theorem det_ne_zero_of_not_collinear {p q r : ℝ × ℝ} (h : ¬Collinear ℝ {p, q, r}) :
    det (q - p) (r - p) ≠ 0 := by
  intro h0
  apply h
  rw [collinear_iff_of_mem (p₀ := p) (by simp)]
  simp only [det, Prod.fst_sub, Prod.snd_sub] at h0
  by_cases hq : q = p
  · refine ⟨r - p, ?_⟩
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hq]⟩
    · exact ⟨1, by simp⟩
  · refine ⟨q - p, ?_⟩
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · by_cases h1 : q.1 - p.1 = 0
      · have h2 : q.2 - p.2 ≠ 0 := by
          intro h2
          exact hq (Prod.ext (by linarith) (by linarith))
        refine ⟨(x.2 - p.2) / (q.2 - p.2), ?_⟩
        have e1 : x.1 - p.1 = 0 := by
          rw [h1, zero_mul, zero_sub, neg_eq_zero] at h0
          exact (mul_eq_zero.1 h0).resolve_left h2
        ext
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, h1,
            mul_zero]
          linarith
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          field_simp
          ring
      · refine ⟨(x.1 - p.1) / (q.1 - p.1), ?_⟩
        ext
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          field_simp
          ring
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
          field_simp
          linarith

/-- A triangle is convex. -/
theorem IsTriangle.convex {T : Set (ℝ × ℝ)} (h : IsTriangle T) : Convex ℝ T := by
  obtain ⟨p, q, r, _, rfl⟩ := h
  exact convex_convexHull ℝ _

/-- A triangle is closed. -/
theorem IsTriangle.isClosed {T : Set (ℝ × ℝ)} (h : IsTriangle T) : IsClosed T := by
  obtain ⟨p, q, r, _, rfl⟩ := h
  have hfin : ({p, q, r} : Set (ℝ × ℝ)).Finite := by simp
  exact hfin.isClosed_convexHull ℝ

/-- A triangle has positive area. -/
theorem IsTriangle.volume_pos {T : Set (ℝ × ℝ)} (h : IsTriangle T) : 0 < volume T := by
  obtain ⟨p, q, r, hnc, rfl⟩ := h
  rw [volume_triangle, ENNReal.ofReal_pos]
  exact div_pos (abs_pos.2 (det_ne_zero_of_not_collinear hnc)) two_pos

/-- A triangle has finite area. -/
theorem IsTriangle.volume_ne_top {T : Set (ℝ × ℝ)} (h : IsTriangle T) : volume T ≠ ⊤ := by
  obtain ⟨p, q, r, hnc, rfl⟩ := h
  rw [volume_triangle]
  exact ENNReal.ofReal_ne_top

/-- A triangle over `K` is a triangle. -/
theorem IsTriangleOver.isTriangle {K : Subfield ℝ} {T : Set (ℝ × ℝ)} (h : IsTriangleOver K T) :
    IsTriangle T := by
  obtain ⟨p, q, r, hnc, hT⟩ := h
  exact ⟨_, _, _, hnc, hT⟩

/-- Every triangle is a triangle over `K = ℝ`. -/
theorem IsTriangle.over_top {T : Set (ℝ × ℝ)} (h : IsTriangle T) :
    IsTriangleOver (⊤ : Subfield ℝ) T := by
  obtain ⟨p, q, r, hnc, hT⟩ := h
  exact ⟨(⟨p.1, trivial⟩, ⟨p.2, trivial⟩), (⟨q.1, trivial⟩, ⟨q.2, trivial⟩),
    (⟨r.1, trivial⟩, ⟨r.2, trivial⟩), hnc, hT⟩

/-- **Area is additive over a dissection** (Lebesgue measure): `Area S = Σ Area (T i)`. -/
theorem IsDissection.volume_eq_sum {ι : Type*} [Fintype ι] {S : Set (ℝ × ℝ)}
    {T : ι → Set (ℝ × ℝ)} (hT : IsDissection S T) : volume S = ∑ i, volume (T i) := by
  rw [← hT.union, volume_iUnion_of_disjoint_interiors T (fun i => (hT.triangle i).convex)
    (fun i => (hT.triangle i).isClosed) hT.disjoint, tsum_fintype]

/-- Area is additive over a dissection, as an identity of real numbers. -/
theorem IsDissection.toReal_volume_eq_sum {ι : Type*} [Fintype ι] {S : Set (ℝ × ℝ)}
    {T : ι → Set (ℝ × ℝ)} (hT : IsDissection S T) :
    (volume S).toReal = ∑ i, (volume (T i)).toReal := by
  rw [hT.volume_eq_sum, ENNReal.toReal_sum (fun i _ => (hT.triangle i).volume_ne_top)]

/-- `par d` commutes with negation. -/
theorem par_neg (d w : ℝ × ℝ) : par d (-w) = -par d w := by
  unfold par
  have e : det d (-w) = -det d w := by
    simp only [det, Prod.fst_neg, Prod.snd_neg]; ring
  rw [e]
  by_cases h : det d w = 0 <;> simp [h]

/-! ### The inclusion `K² → ℝ²` -/

section emb

variable (K : Subfield ℝ)

/-- The coordinates of `emb K x`. -/
theorem emb_apply (x : K × K) : emb K x = ((x.1 : ℝ), (x.2 : ℝ)) := rfl

/-- The inclusion `K² → ℝ²` is injective. -/
theorem emb_injective : Function.Injective (emb K) := by
  intro x y h
  rw [emb_apply, emb_apply, Prod.mk.injEq] at h
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

/-- The inclusion `K² → ℝ²` commutes with `det`. -/
theorem det_emb (x y : K × K) : det (emb K x) (emb K y) = ((det x y : K) : ℝ) := by
  simp [det, emb_apply]

/-- The inclusion `K² → ℝ²` commutes with `par`. -/
theorem par_emb [DecidableEq K] (d w : K × K) : emb K (par d w) = par (emb K d) (emb K w) := by
  unfold par
  rw [det_emb]
  by_cases h : det d w = 0
  · simp [h]
  · have h' : ((det d w : K) : ℝ) ≠ 0 := fun h0 => h (by exact_mod_cast h0)
    simp [h, h']

/-- A triangle over `K` has counter-clockwise vertices in `K²`. -/
theorem IsTriangleOver.exists_ccw {T : Set (ℝ × ℝ)} (h : IsTriangleOver K T) :
    ∃ p q r : K × K, 0 < det (emb K q - emb K p) (emb K r - emb K p) ∧
      T = convexHull ℝ {emb K p, emb K q, emb K r} := by
  obtain ⟨p, q, r, hnc, hT⟩ := h
  rcases lt_or_gt_of_ne (det_ne_zero_of_not_collinear hnc) with hneg | hpos
  · refine ⟨p, r, q, ?_, ?_⟩
    · have : det (emb K r - emb K p) (emb K q - emb K p)
          = -det (emb K q - emb K p) (emb K r - emb K p) := by
        simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
      rw [this]; linarith
    · rw [hT]
      congr 1
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · exact ⟨p, q, r, hpos, hT⟩

end emb

/-! ### Lemma 4.1, the Main Theorem and Stein's conjecture -/

/-- The sum of `f` over a flattened list of lists is the sum of the sums over the lists. -/
private theorem sum_flatten_map {α β γ : Type*} [AddCommMonoid γ] (l : List α) (s : α → List β)
    (f : β → γ) :
    (((l.map s).flatten).map f).sum = (l.map (fun i => ((s i).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append, List.sum_cons,
      ih]

/-- The family of side sequences of the triangles `p i, q i, r i`. -/
def sideFamily {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (p q r : ι → K × K) :
    List (List (K × K)) :=
  (Finset.univ : Finset ι).toList.map (fun i => sideSeq (p i) (q i) (r i))

/-- **Lemma 4.1, second sentence.**  If `S` lies on the left of its oriented boundary and the
boundary is special, then the side sequences of the counter-clockwise triangles of a dissection
of `S` form a balanced family (here: over any subfield `K` of `ℝ` containing the coordinates of
the vertices of the triangles). -/
theorem balanced_of_special {κ : Type*} [Fintype κ] {S : Set (ℝ × ℝ)} {A B : κ → ℝ × ℝ}
    (hS : OrientedBoundary S A B) (hsp : Special A B) (K : Subfield ℝ) [DecidableEq K]
    {ι : Type*} [Fintype ι] (p q r : ι → K × K)
    (hD : ∀ i, 0 < det (emb K (q i) - emb K (p i)) (emb K (r i) - emb K (p i)))
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (convexHull ℝ {emb K (p i), emb K (q i), emb K (r i)}))
        (interior (convexHull ℝ {emb K (p j), emb K (q j), emb K (r j)})))
    (hU : (⋃ i, convexHull ℝ {emb K (p i), emb K (q i), emb K (r i)}) = S) :
    Balanced (sideFamily p q r) := by
  intro d hd
  apply emb_injective K
  have hd' : emb K d ≠ 0 := fun h => hd (emb_injective K (by rw [h, map_zero]))
  have hbal := balance hS (fun i => emb K (p i)) (fun i => emb K (q i)) (fun i => emb K (r i))
    hD hdisj hU (emb K d) hd'
  rw [hsp _ hd'] at hbal
  rw [map_zero, map_list_sum, List.map_map, sideFamily, sum_flatten_map, Finset.sum_map_toList,
    ← hbal]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sideSeq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, par_emb, map_sub, add_zero, add_assoc]

/-- **Theorem 1.2 (Main Theorem), for a set on the left of its oriented boundary.**
Let `S ⊆ ℝ²` lie on the left of its oriented polygonal boundary `A k → B k`
(`OrientedBoundary`), let the boundary be special, and let `T i` be a dissection of `S` into
triangles whose vertices have coordinates in the subfield `K` of `ℝ`.  Let `v` be any valuation
on `K` (Mathlib's multiplicative convention: `v (x + y) ≤ max (v x) (v y)`; the paper's
`v(x) ≥ ν` reads `v x ≤ γ`).  If `a i = 2 Area (T i)` and `a₀ = 2 Area S` (Lebesgue measure,
as elements of `K`) and `v (a i) ≤ γ` for all `i`, then `v a₀ ≤ v 2 * γ`.
In the paper's additive notation: `v(2 Area S) ≥ v(2) + min_i v(2 Area T_i)`. -/
theorem main_theorem_of_orientedBoundary {κ : Type*} [Fintype κ] {S : Set (ℝ × ℝ)}
    {A B : κ → ℝ × ℝ} (hS : OrientedBoundary S A B) (hsp : Special A B)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection S T)
    (K : Subfield ℝ) (hK : ∀ i, IsTriangleOver K (T i))
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (γ : Γ₀)
    (a : ι → K) (ha : ∀ i, (a i : ℝ) = 2 * (volume (T i)).toReal) (hγ : ∀ i, v (a i) ≤ γ)
    (a₀ : K) (ha₀ : (a₀ : ℝ) = 2 * (volume S).toReal) :
    v a₀ ≤ v 2 * γ := by
  classical
  choose p q r hD hTeq using fun i => (hK i).exists_ccw K
  have hT' : T = fun i => convexHull ℝ {emb K (p i), emb K (q i), emb K (r i)} := funext hTeq
  subst hT'
  -- `a i` is the determinant of the triangle `i`
  have hdet : ∀ i, det (q i - p i) (r i - p i) = a i := by
    intro i
    apply Subtype.ext
    rw [ha i, volume_triangle, ENNReal.toReal_ofReal (by positivity), ← det_emb, map_sub,
      map_sub, abs_of_pos (hD i)]
    ring
  have hbal : Balanced (sideFamily p q r) :=
    balanced_of_special hS hsp K p q r hD hT.disjoint hT.union
  have hclosed : Closed (sideFamily p q r) := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    exact sum_sideSeq _ _ _
  have hflat : Flat v γ (sideFamily p q r) := by
    intro c hc w hw w' hw'
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rcases det_sideSeq _ _ _ w w' hw hw' with h | h | h
    · rw [h, hdet]; exact hγ i
    · rw [h, hdet, Valuation.map_neg]; exact hγ i
    · rw [h, map_zero]; exact zero_le
  have hSF : Stein.S (sideFamily p q r) = a₀ := by
    apply Subtype.ext
    rw [ha₀, hT.toReal_volume_eq_sum, Finset.mul_sum, Stein.S, sideFamily, List.map_map,
      Finset.sum_map_toList]
    simp only [Function.comp_apply, bracket_sideSeq, hdet]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl (fun i _ => ha i)
  rw [← hSF]
  exact theorem_M v γ _ hclosed hflat hbal

/-- **Corollary 1.3 (Stein's conjecture), for a set on the left of its oriented boundary.**
If `S` lies on the left of its oriented polygonal boundary and the boundary is special, then
every dissection of `S` into finitely many triangles of equal area (Lebesgue measure) has an
even number of triangles. -/
theorem stein_conjecture_of_orientedBoundary {κ : Type*} [Fintype κ] {S : Set (ℝ × ℝ)}
    {A B : κ → ℝ × ℝ} (hS : OrientedBoundary S A B) (hsp : Special A B)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection S T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even (Fintype.card ι) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp
  -- a valuation on `K = ℝ` with `v 2 < 1` (Lemma 2.1)
  obtain ⟨O, hO⟩ := exists_valuation_two_pos (⊤ : Subfield ℝ)
  set v := O.valuation with hv
  let K : Subfield ℝ := ⊤
  let a : K := ⟨2 * (volume (T i₀)).toReal, trivial⟩
  let a₀ : K := ⟨2 * (volume S).toReal, trivial⟩
  have ha_ne : a ≠ 0 := by
    intro h
    have h' : 2 * (volume (T i₀)).toReal = 0 := congrArg Subtype.val h
    have hpos := ENNReal.toReal_pos (hT.triangle i₀).volume_pos.ne'
      (hT.triangle i₀).volume_ne_top
    linarith
  have hmain := main_theorem_of_orientedBoundary hS hsp T hT K
    (fun i => (hT.triangle i).over_top) v (v a) (fun _ => a)
    (fun i => by rw [heq i i₀]) (fun _ => le_refl _) a₀ rfl
  -- `a₀ = n * a`
  have hsum : a₀ = (Fintype.card ι : K) * a := by
    apply Subtype.ext
    show 2 * (volume S).toReal = ((Fintype.card ι : K) : ℝ) * (2 * (volume (T i₀)).toReal)
    rw [hT.toReal_volume_eq_sum, Finset.sum_congr rfl (fun i _ => by rw [heq i i₀]),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum, map_mul] at hmain
  have hva : v a ≠ 0 := (Valuation.ne_zero_iff v).2 ha_ne
  have hn : v (Fintype.card ι : K) ≤ v 2 := (mul_le_mul_iff_left₀ (zero_lt_iff.2 hva)).1 hmain
  -- an odd `n` would give `v 1 < 1`
  by_contra hodd
  obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 hodd
  have hm1 : v (m : K) ≤ 1 := by
    have : (m : K) ∈ O := natCast_mem O m
    exact (ValuationSubring.valuation_le_one_iff O _).2 this
  have h2m : v ((2 : K) * (m : K)) < 1 := by
    rw [map_mul]
    calc v 2 * v (m : K) ≤ v 2 * 1 := by gcongr
      _ = v 2 := mul_one _
      _ < 1 := hO
  have hone : (1 : K) = (Fintype.card ι : K) - 2 * (m : K) := by
    rw [hm]; push_cast; ring
  have h1 : v (1 : K) < 1 := by
    rw [hone]
    exact lt_of_le_of_lt (Valuation.map_sub v _ _) (max_lt (lt_of_le_of_lt hn hO) h2m)
  rw [map_one] at h1
  exact lt_irrefl _ h1

end

end Stein
