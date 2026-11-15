import Stein.Algebra.Sequences

/-!
# The algebraic core (paper, §5)

* `lemma_T`   : Lemma 5.1 (Lemma T);
* `theorem_M` : Theorem 5.2 (Theorem M): a closed, `γ`-flat, balanced family `F` satisfies
  `v (S F) ≤ v 2 * γ` (additively: `v(S(F)) ≥ v(2) + ν`), over any field and for any valuation.

The proof of Theorem M follows the paper: induction on the number of entries;
Step 1 (`exists_partner`): a longest entry `u` has a parallel, equally long partner `u' = t u`,
found from balance; Step 2 (`step_join`): Join the two sequences containing `u` and `u'`,
flatness being kept by Lemma T; Steps 3 and 4 (`merge`): Swap `u'` next to `u` (cost
`2 det (σ(B), u')`, `bracket_move`) and Add them (`bracket_add`, free since `u ∥ u'`).
Valuations are written multiplicatively (Mathlib's convention), which reverses the paper's
inequalities.
-/

namespace Stein

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-! ### Lemma T -/

/-- The valuation computation in Lemma T: if `a x = b y' - b' y` with `a ≠ 0` and `b / a`,
`b' / a` of valuation `≤ 1`, then `v x ≤ max (v y) (v y')`. -/
private theorem lemma_T_aux (v : Valuation K Γ₀) {a b b' x y y' : K} (ha : a ≠ 0) (hb : v b ≤ v a)
    (hb' : v b' ≤ v a) (h : a * x = b * y' - b' * y) : v x ≤ max (v y) (v y') := by
  have h0 : v a * v x = v (b * y' - b' * y) := by rw [← map_mul, h]
  have h1 : v a * v x ≤ v a * max (v y) (v y') := by
    rw [h0]
    refine (v.map_sub _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_mul' hb (le_max_right _ _)
    · rw [map_mul]; exact mul_le_mul' hb' (le_max_left _ _)
  exact le_of_mul_le_mul_left h1 (zero_lt_iff.mpr (v.ne_zero_iff.mpr ha))

/-- If the size of `u ≠ 0` is the valuation of `x` (one of its coordinates), then `x ≠ 0`. -/
private theorem ne_zero_of_vnorm_eq (v : Valuation K Γ₀) {u : K × K} (hu : u ≠ 0) {x : K}
    (h : vnorm v u = v x) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact hu ((vnorm_eq_zero_iff v u).mp h)

/-- **Lemma 5.1 (Lemma T).** Let `u, w, w' ∈ K²` with `u ≠ 0` and `u` at least as long as `w`
and `w'` (paper: `v(u) ≤ v(w)`, `v(u) ≤ v(w')`; multiplicatively `vnorm v w ≤ vnorm v u`, where
`vnorm v w = max (v w.1) (v w.2)`). Then `v(det (w, w')) ≥ min (v(det (u, w)), v(det (u, w')))`,
i.e. multiplicatively `v (det w w') ≤ max (v (det u w)) (v (det u w'))`. -/
theorem lemma_T (v : Valuation K Γ₀) (u w w' : K × K) (hu : u ≠ 0)
    (hw : vnorm v w ≤ vnorm v u) (hw' : vnorm v w' ≤ vnorm v u) :
    v (det w w') ≤ max (v (det u w)) (v (det u w')) := by
  rcases vnorm_eq v u with h | h
  · -- the first coordinate of `u` is the long one:
    -- `u₁ det (w, w') = w₁ det (u, w') - w'₁ det (u, w)`
    have hu1 : u.1 ≠ 0 := ne_zero_of_vnorm_eq v hu h
    exact lemma_T_aux v hu1 ((le_max_left _ _).trans (hw.trans h.le))
      ((le_max_left _ _).trans (hw'.trans h.le)) (by simp only [det]; ring)
  · -- the second coordinate of `u` is the long one
    have hu2 : u.2 ≠ 0 := ne_zero_of_vnorm_eq v hu h
    exact lemma_T_aux v hu2 ((le_max_right _ _).trans (hw.trans h.le))
      ((le_max_right _ _).trans (hw'.trans h.le)) (by simp only [det]; ring)

/-! ### Auxiliary valuation facts -/

/-- A sum of elements of valuation `< g` has valuation `< g` (consequence of (V3)). -/
private theorem sum_lt_of_forall_lt (v : Valuation K Γ₀) {g : Γ₀} (hg : g ≠ 0) (l : List K)
    (h : ∀ x ∈ l, v x < g) : v l.sum < g := by
  induction l with
  | nil => simpa using zero_lt_iff.mpr hg
  | cons a l ih =>
    rw [List.sum_cons]
    exact lt_of_le_of_lt (v.map_add _ _)
      (max_lt (h a (by simp)) (ih (fun x hx => h x (by simp [hx]))))

/-- If `v (det b q) ≤ γ` for every entry `b` of the block `B`, then `v (det (σ(B), q)) ≤ γ`. -/
private theorem map_det_sum_le (v : Valuation K Γ₀) {γ : Γ₀} (B : List (K × K)) (q : K × K)
    (h : ∀ b ∈ B, v (det b q) ≤ γ) : v (det B.sum q) ≤ γ := by
  induction B with
  | nil => simp
  | cons b B ih =>
    rw [List.sum_cons, det_add_left]
    exact v.map_add_le (h b (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-! ### Step 1: a longest entry and its partner -/

/-- Core of Step 1, for a coordinate functional `π` (first or second coordinate) such that
`π u ≠ 0` and `v (π w) ≤ v (π u)` for all other entries `w`: if `u` together with the entries of
`E` on the line `K u` sums to `0`, some entry `u'` of `E` on that line has `v (π u') = v (π u)`.
Otherwise `π u` would be a sum of elements of smaller valuation. -/
private theorem exists_partner_aux [DecidableEq K] (v : Valuation K Γ₀) (π : K × K →+ K) (u : K × K)
    (E : List (K × K)) (hπu : π u ≠ 0) (hπ : ∀ w ∈ E, v (π w) ≤ v (π u))
    (hsum : u + (E.map (par u)).sum = 0) :
    ∃ u' ∈ E, det u u' = 0 ∧ v (π u') = v (π u) := by
  by_contra hcon
  push Not at hcon
  have h1 : π u + ((E.map (par u)).map π).sum = 0 := by
    have := congrArg π hsum
    rwa [map_add, map_list_sum, map_zero] at this
  have h2 : v ((E.map (par u)).map π).sum < v (π u) := by
    apply sum_lt_of_forall_lt v (v.ne_zero_iff.mpr hπu)
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    by_cases hd : det u w = 0
    · simp only [par, hd, ↓reduceIte]
      exact lt_of_le_of_ne (hπ w hw) (hcon w hw hd)
    · simp only [par, hd, ↓reduceIte, map_zero]
      exact zero_lt_iff.mpr (v.ne_zero_iff.mpr hπu)
  have h3 : ((E.map (par u)).map π).sum = - π u := by linear_combination h1
  rw [h3, Valuation.map_neg] at h2
  exact lt_irrefl _ h2

/-- **Theorem M, Step 1 (a longest entry and a partner).** Let `u ≠ 0` be at least as long as
every entry of `E`, and suppose that `u` and the entries of `E` on the line `K u` sum to `0`
(balance in the direction `u`). Then `E` contains an entry `u' ≠ 0` parallel to `u` and equally
long: `u' = t u` with `v t = 1`. The latter is expressed by `v (det u w) = v (det u' w)` for
all `w` (as `det (u', w) = t det (u, w)`). -/
theorem exists_partner [DecidableEq K] (v : Valuation K Γ₀) (u : K × K) (E : List (K × K))
    (hu : u ≠ 0) (hE : ∀ w ∈ E, vnorm v w ≤ vnorm v u) (hsum : u + (E.map (par u)).sum = 0) :
    ∃ u' ∈ E, u' ≠ 0 ∧ det u u' = 0 ∧ ∀ w, v (det u w) = v (det u' w) := by
  rcases vnorm_eq v u with h | h
  · have hu1 : u.1 ≠ 0 := ne_zero_of_vnorm_eq v hu h
    obtain ⟨u', hu'E, hdet, hv⟩ := exists_partner_aux v (AddMonoidHom.fst K K) u E hu1
      (fun w hw => (le_max_left _ _).trans ((hE w hw).trans h.le)) hsum
    have hv' : v u'.1 = v u.1 := hv
    have hu'1 : u'.1 ≠ 0 := v.ne_zero_iff.mp (by rw [hv']; exact v.ne_zero_iff.mpr hu1)
    refine ⟨u', hu'E, fun h0 => hu'1 (by rw [h0]; rfl), hdet, fun w => ?_⟩
    have hid : u.1 * det u' w = u'.1 * det u w - w.1 * det u u' := by simp only [det]; ring
    rw [hdet, mul_zero, sub_zero] at hid
    have h3 := congrArg v hid
    rw [map_mul, map_mul, hv'] at h3
    exact (mul_left_cancel₀ (v.ne_zero_iff.mpr hu1) h3).symm
  · have hu2 : u.2 ≠ 0 := ne_zero_of_vnorm_eq v hu h
    obtain ⟨u', hu'E, hdet, hv⟩ := exists_partner_aux v (AddMonoidHom.snd K K) u E hu2
      (fun w hw => (le_max_right _ _).trans ((hE w hw).trans h.le)) hsum
    have hv' : v u'.2 = v u.2 := hv
    have hu'2 : u'.2 ≠ 0 := v.ne_zero_iff.mp (by rw [hv']; exact v.ne_zero_iff.mpr hu2)
    refine ⟨u', hu'E, fun h0 => hu'2 (by rw [h0]; rfl), hdet, fun w => ?_⟩
    have hid : u.2 * det u' w = u'.2 * det u w - w.2 * det u u' := by simp only [det]; ring
    rw [hdet, mul_zero, sub_zero] at hid
    have h3 := congrArg v hid
    rw [map_mul, map_mul, hv'] at h3
    exact (mul_left_cancel₀ (v.ne_zero_iff.mpr hu2) h3).symm

/-! ### Step 2: Join -/

/-- **Theorem M, Step 2 (Join).** Let `u ∈ c` be a longest entry and `u' ∈ y` its partner
(`v (det u w) = v (det u' w)` for all `w`). Replacing the two sequences `c, y` by `c y` keeps the
family closed, `γ`-flat (by Lemma T) and balanced (same entries), and does not change `S`
(Lemma 3.1 (a)). -/
theorem step_join [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (c y : List (K × K))
    (R : List (List (K × K))) (u u' : K × K) (hu : u ≠ 0) (huc : u ∈ c) (hu'y : u' ∈ y)
    (hmax : ∀ w ∈ c ++ y, vnorm v w ≤ vnorm v u) (hval : ∀ w, v (det u w) = v (det u' w))
    (hc : Closed (c :: y :: R)) (hf : Flat v γ (c :: y :: R)) (hb : Balanced (c :: y :: R)) :
    Closed ((c ++ y) :: R) ∧ Flat v γ ((c ++ y) :: R) ∧ Balanced ((c ++ y) :: R) ∧
      S ((c ++ y) :: R) = S (c :: y :: R) ∧
      ((c ++ y) :: R).flatten = (c :: y :: R).flatten := by
  have hjoin := bracket_join c y (hc c (by simp)) (hc y (by simp))
  have hflat : ((c ++ y) :: R).flatten = (c :: y :: R).flatten := by simp
  -- the mixed pairs, by Lemma T
  have hmix : ∀ w ∈ c, ∀ w' ∈ y, v (det w w') ≤ γ := by
    intro w hw w' hw'
    refine (lemma_T v u w w' hu (hmax w (by simp [hw])) (hmax w' (by simp [hw']))).trans
      (max_le ?_ ?_)
    · exact hf c (by simp) u huc w hw
    · rw [hval w']
      exact hf y (by simp) u' hu'y w' hw'
  refine ⟨?_, ?_, ?_, ?_, hflat⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hjoin.1
    · exact hc x (by simp [hx])
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · intro w hw w' hw'
      rcases List.mem_append.mp hw with hw | hw <;> rcases List.mem_append.mp hw' with hw' | hw'
      · exact hf c (by simp) w hw w' hw'
      · exact hmix w hw w' hw'
      · rw [det_swap, Valuation.map_neg]
        exact hmix w' hw' w hw
      · exact hf y (by simp) w hw w' hw'
    · exact hf x (by simp [hx])
  · intro d hd
    rw [hflat]
    exact hb d hd
  · rw [S_cons, S_cons, S_cons, hjoin.2, add_assoc]

/-! ### Steps 3 and 4: Swap and Add -/

/-- Two non-zero parallel vectors `p, q` may be replaced by their sum without changing the sum
of the entries on any line: `par d (p + q) = par d p + par d q`. -/
theorem par_add_of_parallel [DecidableEq K] (d p q : K × K) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : det p q = 0) : par d (p + q) = par d p + par d q := by
  have h1 : p.1 * det d q = q.1 * det d p := by
    have h : p.1 * det d q - q.1 * det d p = d.1 * det p q := by simp only [det]; ring
    rw [hpq, mul_zero, sub_eq_zero] at h
    exact h
  have h2 : p.2 * det d q = q.2 * det d p := by
    have h : p.2 * det d q - q.2 * det d p = d.2 * det p q := by simp only [det]; ring
    rw [hpq, mul_zero, sub_eq_zero] at h
    exact h
  have hadd : det d (p + q) = det d p + det d q := det_add_right d p q
  by_cases hdp : det d p = 0
  · have hdq : det d q = 0 := by
      rw [hdp, mul_zero] at h1 h2
      by_contra h
      apply hp
      refine Prod.ext ?_ ?_
      · simpa [h] using h1
      · simpa [h] using h2
    simp [par, hadd, hdp, hdq]
  · have hdq : det d q ≠ 0 := by
      intro h
      rw [h, mul_zero] at h1 h2
      apply hq
      refine Prod.ext ?_ ?_
      · simpa [hdp] using h1.symm
      · simpa [hdp] using h2.symm
    by_cases hs : det d (p + q) = 0
    · have h3 : det d q = - det d p := by
        rw [hadd] at hs
        linear_combination hs
      have h0 : p + q = 0 := by
        rw [h3] at h1 h2
        refine Prod.ext ?_ ?_
        · have h4 : (p.1 + q.1) * det d p = 0 := by linear_combination -h1
          simpa [hdp] using h4
        · have h4 : (p.2 + q.2) * det d p = 0 := by linear_combination -h2
          simpa [hdp] using h4
      simp [par, hdp, hdq, h0]
    · simp [par, hdp, hdq, hs]

/-- **Theorem M, Steps 3 and 4 (Swap, then Add).** Let `p, q` be two non-zero parallel entries
of the same sequence `A p B₁ q B₂` of a closed, `γ`-flat, balanced family. Moving `q` next to `p`
by swaps (`bracket_move`, Lemma 3.1 (b)) and replacing `p, q` by `p + q` (`bracket_add`,
Lemma 3.1 (c)) gives a closed, `γ`-flat, balanced family with one entry fewer, and `S` changes by
`2 det (σ(B₁), q) + det (p, q) = 2 det (σ(B₁), q)`, of valuation `≤ v 2 * γ`.
(The statement is symmetric in `p, q`, so it does not matter which of the two is the longest
entry `u`.) -/
theorem merge [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (A B₁ B₂ : List (K × K))
    (R : List (List (K × K))) (p q : K × K) (c : List (K × K))
    (hcdef : c = A ++ p :: (B₁ ++ q :: B₂)) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : det p q = 0)
    (hc : Closed (c :: R)) (hf : Flat v γ (c :: R)) (hb : Balanced (c :: R)) :
    Closed ((A ++ (p + q) :: (B₁ ++ B₂)) :: R) ∧
      Flat v γ ((A ++ (p + q) :: (B₁ ++ B₂)) :: R) ∧
      Balanced ((A ++ (p + q) :: (B₁ ++ B₂)) :: R) ∧
      ((A ++ (p + q) :: (B₁ ++ B₂)) :: R).flatten.length + 1 = (c :: R).flatten.length ∧
      v (S (c :: R) - S ((A ++ (p + q) :: (B₁ ++ B₂)) :: R)) ≤ v 2 * γ := by
  subst hcdef
  have hpm : p ∈ A ++ p :: (B₁ ++ q :: B₂) := by simp
  have hqm : q ∈ A ++ p :: (B₁ ++ q :: B₂) := by simp
  -- every new entry is an old entry or `p + q`
  have hmem : ∀ w ∈ A ++ (p + q) :: (B₁ ++ B₂), w ∈ A ++ p :: (B₁ ++ q :: B₂) ∨ w = p + q := by
    intro w hw
    simp only [List.mem_append, List.mem_cons] at hw ⊢
    tauto
  have hfc := hf _ List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- closed: Swap and Add preserve `σ`
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [← sum_add, ← sum_move]
      exact hc _ List.mem_cons_self
    · exact hc x (by simp [hx])
  · -- flat: `det (p + q, w) = det (p, w) + det (q, w)`
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · intro w hw w' hw'
      rcases hmem w hw with hw | rfl <;> rcases hmem w' hw' with hw' | rfl
      · exact hfc w hw w' hw'
      · rw [det_add_right]
        exact v.map_add_le (hfc w hw p hpm) (hfc w hw q hqm)
      · rw [det_add_left]
        exact v.map_add_le (hfc p hpm w' hw') (hfc q hqm w' hw')
      · rw [det_self, map_zero]
        exact zero_le
    · exact hf x (by simp [hx])
  · -- balanced: on every line two parallel entries were replaced by their sum
    intro d hd
    rw [← hb d hd]
    simp only [List.flatten_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      par_add_of_parallel d p q hp hq hpq]
    abel
  · simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega
  · -- the cost: `2 det (σ(B₁), q) + det (p, q)`
    have hS : S ((A ++ p :: (B₁ ++ q :: B₂)) :: R) - S ((A ++ (p + q) :: (B₁ ++ B₂)) :: R)
        = 2 * det B₁.sum q := by
      rw [S_cons, S_cons, bracket_move, bracket_add, hpq]
      ring
    rw [hS, map_mul]
    refine mul_le_mul' le_rfl (map_det_sum_le v B₁ q (fun b hbB => hfc b ?_ q hqm))
    simp [hbB]

/-! ### Theorem M -/

/-- **Theorem M, one round of Steps 1–4.** If `u ≠ 0` is a longest entry of the closed, `γ`-flat,
balanced family `(A u B) :: R`, there is a closed, `γ`-flat, balanced family `F'` with one entry
fewer whose `S` differs from the old one by an element of valuation `≤ v 2 * γ`. -/
private theorem step [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (A B : List (K × K))
    (R : List (List (K × K))) (u : K × K) (hu : u ≠ 0)
    (hmax : ∀ c ∈ (A ++ u :: B) :: R, ∀ w ∈ c, vnorm v w ≤ vnorm v u)
    (hc : Closed ((A ++ u :: B) :: R)) (hf : Flat v γ ((A ++ u :: B) :: R))
    (hb : Balanced ((A ++ u :: B) :: R)) :
    ∃ F' : List (List (K × K)),
      F'.flatten.length + 1 = ((A ++ u :: B) :: R).flatten.length ∧
      Closed F' ∧ Flat v γ F' ∧ Balanced F' ∧ v (S ((A ++ u :: B) :: R) - S F') ≤ v 2 * γ := by
  -- Step 1: the partner `u'`, among the other entries
  have hbal := hb u hu
  simp only [List.flatten_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
    par_self] at hbal
  obtain ⟨u', hu'E, hu'0, hdet, hval⟩ := exists_partner v u (A ++ B ++ R.flatten) hu
    (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hmax _ List.mem_cons_self w (by
          rcases List.mem_append.mp hw with hw | hw <;> simp [hw])
      · obtain ⟨y, hy, hwy⟩ := List.mem_flatten.mp hw
        exact hmax y (by simp [hy]) w hwy)
    (by
      simp only [List.map_append, List.sum_append]
      rw [← hbal]
      abel)
  have hdet' : det u' u = 0 := by rw [det_swap, hdet, neg_zero]
  rcases List.mem_append.mp hu'E with hu'AB | hu'R
  · rcases List.mem_append.mp hu'AB with hu'A | hu'B
    · -- `u'` precedes `u` in the same sequence
      obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hu'A
      obtain ⟨h1, h2, h3, h4, h5⟩ := merge v γ A₁ A₂ B R u' u _ (by simp) hu'0 hu hdet' hc hf hb
      exact ⟨_, h4, h1, h2, h3, h5⟩
    · -- `u'` follows `u` in the same sequence
      obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hu'B
      obtain ⟨h1, h2, h3, h4, h5⟩ := merge v γ A B₁ B₂ R u u' _ rfl hu hu'0 hdet hc hf hb
      exact ⟨_, h4, h1, h2, h3, h5⟩
  · -- `u'` lies in another sequence `y`: Step 2 (Join) first
    obtain ⟨y, hyR, hu'y⟩ := List.mem_flatten.mp hu'R
    obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hyR
    obtain ⟨Y₁, Y₂, rfl⟩ := List.append_of_mem hu'y
    have hperm : ((A ++ u :: B) :: (R₁ ++ (Y₁ ++ u' :: Y₂) :: R₂)).Perm
        ((A ++ u :: B) :: (Y₁ ++ u' :: Y₂) :: (R₁ ++ R₂)) := List.Perm.cons _ List.perm_middle
    obtain ⟨j1, j2, j3, j4, j5⟩ := step_join v γ (A ++ u :: B) (Y₁ ++ u' :: Y₂) (R₁ ++ R₂) u u' hu
      (by simp) (by simp)
      (by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hmax _ List.mem_cons_self w hw
        · exact hmax (Y₁ ++ u' :: Y₂) (by simp) w hw)
      hval (hc.perm hperm) (hf.perm hperm) (hb.perm hperm)
    obtain ⟨h1, h2, h3, h4, h5⟩ := merge v γ A (B ++ Y₁) Y₂ (R₁ ++ R₂) u u' _ (by simp) hu hu'0
      hdet j1 j2 j3
    refine ⟨_, ?_, h1, h2, h3, ?_⟩
    · rw [h4, j5, hperm.flatten.length_eq]
    · rw [S_perm hperm, ← j4]
      exact h5

/-- The reduction step of Theorem M for an arbitrary family having a non-zero entry: choose a
longest entry `u` (it is non-zero), bring its sequence to the front, and apply `step`. -/
private theorem reduce [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (F : List (List (K × K)))
    (hc : Closed F) (hf : Flat v γ F) (hb : Balanced F)
    (hne : ∃ c ∈ F, ∃ w ∈ c, w ≠ 0) :
    ∃ F' : List (List (K × K)), F'.flatten.length + 1 = F.flatten.length ∧
      Closed F' ∧ Flat v γ F' ∧ Balanced F' ∧ v (S F - S F') ≤ v 2 * γ := by
  obtain ⟨c₀, hc₀, w₀, hw₀, hw₀ne⟩ := hne
  -- a longest entry
  have hnonempty : (F.flatten.toFinset).Nonempty :=
    ⟨w₀, List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨c₀, hc₀, hw₀⟩)⟩
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image _ (vnorm v) hnonempty
  rw [List.mem_toFinset] at hu
  have hmax' : ∀ c ∈ F, ∀ w ∈ c, vnorm v w ≤ vnorm v u := fun c hcF w hw =>
    hmax w (List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨c, hcF, hw⟩))
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h := hmax' c₀ hc₀ w₀ hw₀
    rw [vnorm_zero, le_zero_iff] at h
    exact hw₀ne ((vnorm_eq_zero_iff v w₀).mp h)
  obtain ⟨c, hcF, huc⟩ := List.mem_flatten.mp hu
  obtain ⟨F₁, F₂, rfl⟩ := List.append_of_mem hcF
  obtain ⟨A, B, rfl⟩ := List.append_of_mem huc
  have hperm : (F₁ ++ (A ++ u :: B) :: F₂).Perm ((A ++ u :: B) :: (F₁ ++ F₂)) := List.perm_middle
  obtain ⟨F', h1, h2, h3, h4, h5⟩ := step v γ A B (F₁ ++ F₂) u hu0
    (fun c hcF => hmax' c (hperm.mem_iff.mpr hcF)) (hc.perm hperm) (hf.perm hperm) (hb.perm hperm)
  refine ⟨F', ?_, h2, h3, h4, ?_⟩
  · rw [h1, hperm.flatten.length_eq]
  · rw [S_perm hperm]
    exact h5

/-- **Theorem 5.2 (Theorem M).** If `F` is a `γ`-flat balanced family of closed sequences, then
`v (S F) ≤ v 2 * γ` (paper, additively: if `F` is `ν`-flat and balanced then
`v(S(F)) ≥ v(2) + ν`). Valid over any field and for any valuation.

Proof by induction on the number of entries. If all entries are `0`, then `S F = 0`. Otherwise
`reduce` (Steps 1–4 of the paper) produces a family with one entry fewer whose `S` differs from
`S F` by an element of valuation `≤ v 2 * γ`. -/
theorem theorem_M [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (F : List (List (K × K)))
    (hc : Closed F) (hf : Flat v γ F) (hb : Balanced F) : v (S F) ≤ v 2 * γ := by
  suffices H : ∀ n, ∀ F : List (List (K × K)), F.flatten.length = n → Closed F → Flat v γ F →
      Balanced F → v (S F) ≤ v 2 * γ from H _ F rfl hc hf hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hn hc hf hb
    by_cases hz : ∀ c ∈ F, ∀ w ∈ c, w = 0
    · rw [S_eq_zero_of_forall_zero F hz, map_zero]
      exact zero_le
    · push Not at hz
      obtain ⟨F', hlen, hc', hf', hb', hS⟩ := reduce v γ F hc hf hb hz
      have h1 := ih F'.flatten.length (by omega) F' rfl hc' hf' hb'
      have h2 := v.map_add_le hS h1
      rwa [sub_add_cancel] at h2

end Stein
