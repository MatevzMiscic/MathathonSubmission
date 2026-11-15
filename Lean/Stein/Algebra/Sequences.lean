import Stein.Basic

/-!
# Closed sequences, the three moves, families (paper, §3)

For a finite sequence `c = (c₁, …, c_r)` of vectors of `K²` the paper puts
`σ(c) = Σ cᵢ` (here: `c.sum`, also `Stein.sigma c`) and `[c] = Σ_{i<j} det (cᵢ, cⱼ)`
(here: `Stein.bracket c`).  A sequence is *closed* if `σ(c) = 0`.

* `bracket_append` : formula (1) of the paper;
* `bracket_join`, `bracket_swap`, `bracket_add` : Lemma 3.1 (the three moves);
* `bracket_move` : the iterated swap used in Step 3 of Theorem M;
* `sideSeq`, `bracket_sideSeq`, `det_sideSeq` : triangles, formula (2);
* `S`, `Closed`, `Flat`, `Balanced` : Definition 3.2 (families).
-/

namespace Stein

section Ring

variable {K : Type*} [CommRing K]

/-! ### Bilinearity of `det` -/

/-- `det` is additive in its first argument. -/
theorem det_add_left (a b c : K × K) : det (a + b) c = det a c + det b c := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- `det` is additive in its second argument. -/
theorem det_add_right (a b c : K × K) : det a (b + c) = det a b + det a c := by
  simp only [det, Prod.fst_add, Prod.snd_add]; ring

/-- `det (0, a) = 0`. -/
@[simp] theorem det_zero_left (a : K × K) : det 0 a = 0 := by
  simp [det]

/-- `det (a, 0) = 0`. -/
@[simp] theorem det_zero_right (a : K × K) : det a 0 = 0 := by
  simp [det]

/-- `det (a, a) = 0`. -/
@[simp] theorem det_self (a : K × K) : det a a = 0 := by
  simp only [det]; ring

/-- `det` is antisymmetric: `det (a, b) = - det (b, a)`. -/
theorem det_swap (a b : K × K) : det a b = - det b a := by
  simp only [det]; ring

/-! ### The bracket -/

/-- `σ(c)`, the sum of the entries of the sequence `c` (paper, §3). -/
abbrev sigma (c : List (K × K)) : K × K := c.sum

/-- The bracket `[c] = Σ_{i<j} det (cᵢ, cⱼ)` of a sequence (paper, §3), defined by recursion:
`[a, c] = det (a, σ(c)) + [c]`. -/
def bracket : List (K × K) → K
  | [] => 0
  | a :: c => det a c.sum + bracket c

/-- The bracket of the empty sequence is `0`. -/
@[simp] theorem bracket_nil : bracket ([] : List (K × K)) = 0 := rfl

/-- The defining recursion of the bracket: `[a, c] = det (a, σ(c)) + [c]`. -/
@[simp] theorem bracket_cons (a : K × K) (c : List (K × K)) :
    bracket (a :: c) = det a c.sum + bracket c := rfl

/-- **Formula (1)**: `[c c'] = [c] + [c'] + det (σ(c), σ(c'))`. -/
theorem bracket_append (c c' : List (K × K)) :
    bracket (c ++ c') = bracket c + bracket c' + det c.sum c'.sum := by
  induction c with
  | nil => simp
  | cons a c ih =>
    simp only [List.cons_append, bracket_cons, List.sum_cons, List.sum_append, ih,
      det_add_left, det_add_right]
    ring

/-- **Lemma 3.1 (a), Join.** If `c` and `c'` are closed, then `c c'` is closed and
`[c c'] = [c] + [c']`. -/
theorem bracket_join (c c' : List (K × K)) (hc : c.sum = 0) (hc' : c'.sum = 0) :
    (c ++ c').sum = 0 ∧ bracket (c ++ c') = bracket c + bracket c' := by
  constructor
  · rw [List.sum_append, hc, hc', add_zero]
  · rw [bracket_append, hc, det_zero_left, add_zero]

/-- **Lemma 3.1 (b), Swap.** Exchanging two neighbouring entries `p, q` changes the bracket by
`2 det (p, q)`. -/
theorem bracket_swap (A B : List (K × K)) (p q : K × K) :
    bracket (A ++ p :: q :: B) = bracket (A ++ q :: p :: B) + 2 * det p q := by
  simp only [bracket_append, bracket_cons, List.sum_cons, det_add_right]
  rw [det_swap q p]
  ring

/-- Swap preserves `σ`. -/
theorem sum_swap (A B : List (K × K)) (p q : K × K) :
    (A ++ p :: q :: B).sum = (A ++ q :: p :: B).sum := by
  simp only [List.sum_append, List.sum_cons]
  abel

/-- **Lemma 3.1 (c), Add.** Replacing two neighbouring entries `p, q` by `p + q` changes the
bracket by `det (p, q)` (which is `0` if `p ∥ q`). -/
theorem bracket_add (A B : List (K × K)) (p q : K × K) :
    bracket (A ++ p :: q :: B) = bracket (A ++ (p + q) :: B) + det p q := by
  simp only [bracket_append, bracket_cons, List.sum_cons, det_add_left, det_add_right]
  ring

/-- Add preserves `σ`. -/
theorem sum_add (A B : List (K × K)) (p q : K × K) :
    (A ++ p :: q :: B).sum = (A ++ (p + q) :: B).sum := by
  simp only [List.sum_append, List.sum_cons]
  abel

/-- Iterated Swap: moving an entry `q` to the left across a block `B` costs `2 det (σ(B), q)`.
Proved by induction on the block, one `bracket_swap` per entry. -/
theorem bracket_move_left (A B C : List (K × K)) (q : K × K) :
    bracket (A ++ (B ++ q :: C)) = bracket (A ++ q :: (B ++ C)) + 2 * det B.sum q := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih =>
    have e1 : A ++ (b :: B ++ q :: C) = (A ++ [b]) ++ (B ++ q :: C) := by simp
    have e2 : (A ++ [b]) ++ q :: (B ++ C) = A ++ b :: q :: (B ++ C) := by simp
    rw [e1, ih (A ++ [b]), e2, bracket_swap, List.sum_cons, det_add_left]
    simp only [List.cons_append]
    ring

/-- **Step 3 of Theorem M (Swap, iterated).** If `B` is the block between `u` and `u'`, moving
`u'` next to `u` by swaps of neighbours changes the bracket by `2 det (σ(B), u')`. -/
theorem bracket_move (A B C : List (K × K)) (u u' : K × K) :
    bracket (A ++ u :: (B ++ u' :: C)) = bracket (A ++ u :: u' :: (B ++ C)) + 2 * det B.sum u' := by
  have e1 : A ++ u :: (B ++ u' :: C) = (A ++ [u]) ++ (B ++ u' :: C) := by simp
  have e2 : A ++ u :: u' :: (B ++ C) = (A ++ [u]) ++ u' :: (B ++ C) := by simp
  rw [e1, e2, bracket_move_left]

/-- Moving an entry does not change `σ`. -/
theorem sum_move (A B C : List (K × K)) (u u' : K × K) :
    (A ++ u :: (B ++ u' :: C)).sum = (A ++ u :: u' :: (B ++ C)).sum := by
  simp only [List.sum_append, List.sum_cons]
  abel

/-- The bracket of a sequence of zero vectors is `0`. -/
theorem bracket_eq_zero_of_forall_zero (c : List (K × K)) (h : ∀ w ∈ c, w = 0) :
    bracket c = 0 := by
  induction c with
  | nil => rfl
  | cons a c ih =>
    rw [bracket_cons, h a (by simp), det_zero_left, zero_add]
    exact ih (fun w hw => h w (by simp [hw]))

/-! ### Triangles -/

/-- The side sequence `(q - p, r - q, p - r)` of the triangle with vertices `p, q, r`
(paper, §3, "Triangles"). -/
def sideSeq (p q r : K × K) : List (K × K) := [q - p, r - q, p - r]

/-- The side sequence of a triangle is closed. -/
theorem sum_sideSeq (p q r : K × K) : (sideSeq p q r).sum = 0 := by
  simp only [sideSeq, List.sum_cons, List.sum_nil]
  abel

/-- **Formula (2), first half**: the bracket of the side sequence is `det (q - p, r - p)`,
twice the signed area of the triangle. -/
theorem bracket_sideSeq (p q r : K × K) :
    bracket (sideSeq p q r) = det (q - p) (r - p) := by
  simp only [sideSeq, bracket_cons, bracket_nil, List.sum_cons, List.sum_nil, det, Prod.fst_add,
    Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero]
  ring

/-- **Formula (2), second half**: the determinant of any two entries of the side sequence is
`± det (q - p, r - p)` (or `0`, when the two entries coincide). -/
theorem det_sideSeq (p q r : K × K) (w w' : K × K) (hw : w ∈ sideSeq p q r)
    (hw' : w' ∈ sideSeq p q r) :
    det w w' = det (q - p) (r - p) ∨ det w w' = - det (q - p) (r - p) ∨ det w w' = 0 := by
  simp only [sideSeq, List.mem_cons, List.not_mem_nil, or_false] at hw hw'
  rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
    first
    | (left; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring1)
    | (right; left; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring1)
    | (right; right; simp only [det, Prod.fst_sub, Prod.snd_sub]; ring1)

/-! ### Families -/

/-- `S(F) = Σ_{c ∈ F} [c]` (Definition 3.2). -/
def S (F : List (List (K × K))) : K := (F.map bracket).sum

/-- A family is a list of *closed* sequences (Definition 3.2): every `c ∈ F` has `σ(c) = 0`. -/
def Closed (F : List (List (K × K))) : Prop := ∀ c ∈ F, c.sum = 0

/-- `F` is *balanced* (Definition 3.2): for every line `K d` through `0`, the entries of `F`
(over all sequences) lying on that line sum to `0`. -/
def Balanced [DecidableEq K] (F : List (List (K × K))) : Prop :=
  ∀ d : K × K, d ≠ 0 → (F.flatten.map (par d)).sum = 0

/-- `S (c :: F) = [c] + S F`. -/
theorem S_cons (c : List (K × K)) (F : List (List (K × K))) : S (c :: F) = bracket c + S F := by
  simp [S]

/-- `S` does not depend on the order of the sequences of the family. -/
theorem S_perm {F F' : List (List (K × K))} (h : F.Perm F') : S F = S F' :=
  (h.map bracket).sum_eq

/-- Closedness does not depend on the order of the sequences of the family. -/
theorem Closed.perm {F F' : List (List (K × K))} (hc : Closed F) (h : F.Perm F') : Closed F' :=
  fun c hcF => hc c (h.mem_iff.mpr hcF)

/-- Balance does not depend on the order of the sequences of the family. -/
theorem Balanced.perm [DecidableEq K] {F F' : List (List (K × K))} (hb : Balanced F)
    (h : F.Perm F') : Balanced F' :=
  fun d hd => ((h.flatten.map (par d)).sum_eq).symm.trans (hb d hd)

/-- A family all of whose entries are `0` has `S = 0`. -/
theorem S_eq_zero_of_forall_zero (F : List (List (K × K))) (h : ∀ c ∈ F, ∀ w ∈ c, w = 0) :
    S F = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact bracket_eq_zero_of_forall_zero c (h c hc)

/-- Every vector is parallel to itself: `par u u = u`. -/
@[simp] theorem par_self [DecidableEq K] (u : K × K) : par u u = u := by
  simp [par]

end Ring

section Valuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- `F` is *`γ`-flat* (Definition 3.2; the paper's `ν`-flat, `v(det (w, w')) ≥ ν`, written
multiplicatively): `v (det w w') ≤ γ` for any two entries `w, w'` of the same sequence. -/
def Flat (v : Valuation K Γ₀) (γ : Γ₀) (F : List (List (K × K))) : Prop :=
  ∀ c ∈ F, ∀ w ∈ c, ∀ w' ∈ c, v (det w w') ≤ γ

/-- Flatness does not depend on the order of the sequences of the family. -/
theorem Flat.perm {v : Valuation K Γ₀} {γ : Γ₀} {F F' : List (List (K × K))} (hf : Flat v γ F)
    (h : F.Perm F') : Flat v γ F' :=
  fun c hcF => hf c (h.mem_iff.mpr hcF)

/-- The (multiplicative) size `max (v w₁) (v w₂)` of a vector; the paper's `v(w) = min (v(w₁),
v(w₂))` written multiplicatively.  "`w` is long" means `vnorm v w` is large. -/
def vnorm (v : Valuation K Γ₀) (w : K × K) : Γ₀ := max (v w.1) (v w.2)

/-- The zero vector has size `0`. -/
@[simp] theorem vnorm_zero (v : Valuation K Γ₀) : vnorm v 0 = 0 := by
  simp [vnorm]

/-- Only the zero vector has size `0`. -/
theorem vnorm_eq_zero_iff (v : Valuation K Γ₀) (w : K × K) : vnorm v w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 : v w.1 = 0 := le_antisymm ((le_max_left (v w.1) (v w.2)).trans_eq h) zero_le
    have h2 : v w.2 = 0 := le_antisymm ((le_max_right (v w.1) (v w.2)).trans_eq h) zero_le
    exact Prod.ext (v.zero_iff.mp h1) (v.zero_iff.mp h2)
  · rintro rfl
    exact vnorm_zero v

/-- The size of a vector is the valuation of one of its two coordinates. -/
theorem vnorm_eq (v : Valuation K Γ₀) (w : K × K) : vnorm v w = v w.1 ∨ vnorm v w = v w.2 :=
  max_choice _ _

end Valuation

end Stein
