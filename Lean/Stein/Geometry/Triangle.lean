import Stein.Basic

/-!
# Triangles in the real plane: inequalities, convex hull, area

For a counter-clockwise triangle `p q r` (`0 < det (q - p) (r - p)`):

* `Stein.Tc p q r` / `Stein.To p q r` : the closed / open triangle, given by the three
  inequalities `0 ≤ cross … x` (`0 < cross … x`);
* `Stein.Tc_eq_convexHull` : `convexHull ℝ {p, q, r} = Tc p q r`;
* `Stein.To_subset_interior` : `To p q r ⊆ interior (convexHull ℝ {p, q, r})`;
* `Stein.volume_triangle` (area of a triangle) : the Lebesgue measure of `convexHull ℝ {p, q, r}` is
  `|det (q - p) (r - p)| / 2`, for arbitrary `p q r`;
* `Stein.volume_iUnion_of_disjoint_interiors` : additivity of Lebesgue measure for closed convex
  sets with pairwise disjoint interiors.
-/

open Set Filter Topology MeasureTheory Pointwise

namespace Stein

noncomputable section

/-- The left normal `(-d.2, d.1)` of the vector `d` (`d` rotated by a quarter turn). -/
def nrm (d : ℝ × ℝ) : ℝ × ℝ := (-d.2, d.1)

/-- The closed triangle with counter-clockwise vertices `p, q, r`, as the set of points lying
on the left of (or on) each of the oriented lines `p → q`, `q → r`, `r → p`. -/
def Tc (p q r : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ cross p q x ∧ 0 ≤ cross q r x ∧ 0 ≤ cross r p x}

/-- The open triangle with counter-clockwise vertices `p, q, r`, as the set of points lying
strictly on the left of each of the oriented lines `p → q`, `q → r`, `r → p`. -/
def To (p q r : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < cross p q x ∧ 0 < cross q r x ∧ 0 < cross r p x}

/-- The open triangle is contained in the closed triangle. -/
theorem To_subset_Tc (p q r : ℝ × ℝ) : To p q r ⊆ Tc p q r :=
  fun _ hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- `cross a b` is continuous. -/
theorem cross_continuous (a b : ℝ × ℝ) : Continuous (cross a b) := by
  unfold cross
  fun_prop

/-- `cross a b` is an affine function: it commutes with affine combinations. -/
theorem cross_comb (a b x y : ℝ × ℝ) (s t : ℝ) (hst : s + t = 1) :
    cross a b (s • x + t • y) = s * cross a b x + t * cross a b y := by
  have hs : s = 1 - t := by linarith
  subst hs
  simp only [cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The three functions `cross` of a triangle sum to the constant `det (q - p) (r - p)`. -/
theorem cross_sum (p q r x : ℝ × ℝ) :
    cross p q x + cross q r x + cross r p x = det (q - p) (r - p) := by
  simp only [cross, det, Prod.fst_sub, Prod.snd_sub]
  ring

/-- The open triangle is an open set. -/
theorem isOpen_To (p q r : ℝ × ℝ) : IsOpen (To p q r) := by
  have h1 : IsOpen {x | 0 < cross p q x} := isOpen_lt continuous_const (cross_continuous p q)
  have h2 : IsOpen {x | 0 < cross q r x} := isOpen_lt continuous_const (cross_continuous q r)
  have h3 : IsOpen {x | 0 < cross r p x} := isOpen_lt continuous_const (cross_continuous r p)
  exact h1.inter (h2.inter h3)

/-- The closed triangle is convex. -/
theorem Tc_convex (p q r : ℝ × ℝ) : Convex ℝ (Tc p q r) := by
  intro x hx y hy s t hs ht hst
  refine ⟨?_, ?_, ?_⟩
  · rw [cross_comb _ _ _ _ _ _ hst]
    exact add_nonneg (mul_nonneg hs hx.1) (mul_nonneg ht hy.1)
  · rw [cross_comb _ _ _ _ _ _ hst]
    exact add_nonneg (mul_nonneg hs hx.2.1) (mul_nonneg ht hy.2.1)
  · rw [cross_comb _ _ _ _ _ _ hst]
    exact add_nonneg (mul_nonneg hs hx.2.2) (mul_nonneg ht hy.2.2)

/-- The convex hull of the vertices of a counter-clockwise triangle is the set `Tc p q r` given
by the three inequalities. -/
theorem Tc_eq_convexHull {p q r : ℝ × ℝ} (hD : 0 < det (q - p) (r - p)) :
    convexHull ℝ {p, q, r} = Tc p q r := by
  apply Subset.antisymm
  · apply convexHull_min _ (Tc_convex p q r)
    have hD' := hD
    simp only [det, Prod.fst_sub, Prod.snd_sub] at hD'
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;>
      (simp only [Tc, cross, mem_ofPred_eq]; refine ⟨?_, ?_, ?_⟩ <;> nlinarith)
  · intro x hx
    rw [mem_convexHull_iff]
    intro t ht hconv
    have hp : p ∈ t := ht (by simp)
    have hq : q ∈ t := ht (by simp)
    have hr : r ∈ t := ht (by simp)
    set D := det (q - p) (r - p) with hDdef
    have hsum := cross_sum p q r x
    have key : x = (cross q r x / D) • p + (cross r p x / D) • q + (cross p q x / D) • r := by
      have hD0 : D ≠ 0 := hD.ne'
      have e : D • x = cross q r x • p + cross r p x • q + cross p q x • r := by
        rw [hDdef]
        ext <;> simp only [cross, det, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, Prod.fst_add, Prod.snd_add] <;> ring
      have e2 : x = (1 / D) • (D • x) := by rw [smul_smul, one_div, inv_mul_cancel₀ hD0, one_smul]
      calc x = (1 / D) • (D • x) := e2
        _ = _ := by
          rw [e]
          simp only [smul_add, smul_smul, div_eq_inv_mul, mul_one]
    rw [key]
    have h := hconv.sum_mem (t := Finset.univ) (w := ![cross q r x / D, cross r p x / D,
      cross p q x / D]) (z := ![p, q, r]) ?_ ?_ ?_
    · simpa [Fin.sum_univ_three, add_assoc] using h
    · intro i _
      fin_cases i
      · exact div_nonneg hx.2.1 hD.le
      · exact div_nonneg hx.2.2 hD.le
      · exact div_nonneg hx.1 hD.le
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← add_div, ← add_div, div_eq_one_iff_eq hD.ne']
      linarith
    · intro i _
      fin_cases i <;> simpa

/-- The open triangle `To p q r` consists of interior points of the triangle. -/
theorem To_subset_interior {p q r : ℝ × ℝ} (hD : 0 < det (q - p) (r - p)) :
    To p q r ⊆ interior (convexHull ℝ {p, q, r}) := by
  rw [Tc_eq_convexHull hD]
  exact interior_maximal (To_subset_Tc p q r) (isOpen_To p q r)

/-- `x + δ n → x` as `δ → 0+`. -/
theorem tendsto_add_smul (x n : ℝ × ℝ) :
    Tendsto (fun δ : ℝ => x + δ • n) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  have h : Continuous (fun δ : ℝ => x + δ • n) := by fun_prop
  have h2 := h.tendsto 0
  simp only [zero_smul, add_zero] at h2
  exact h2.mono_left nhdsWithin_le_nhds

/-- `cross a b` along the line `δ ↦ x + δ n`. -/
theorem cross_add_smul (a b x n : ℝ × ℝ) (δ : ℝ) :
    cross a b (x + δ • n) = cross a b x + δ * det (b - a) n := by
  simp only [cross, det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_sub, Prod.snd_sub]
  ring

/-- A non-zero vector `d` of the real plane has `0 < d.1 ^ 2 + d.2 ^ 2`. -/
theorem sq_add_sq_pos {d : ℝ × ℝ} (hd : d ≠ 0) : 0 < d.1 ^ 2 + d.2 ^ 2 := by
  by_contra h
  apply hd
  have h1 : d.1 ^ 2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
  have h2 : d.2 ^ 2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
  exact Prod.ext (by simpa using h1) (by simpa using h2)

/-- An interior point of a set contained in the closed half-plane on the left of `a → b`
(`a ≠ b`) is strictly on the left of `a → b`. -/
private theorem cross_pos_of_mem_interior {a b x : ℝ × ℝ} {s : Set (ℝ × ℝ)} (hab : a ≠ b)
    (hs : ∀ y ∈ s, 0 ≤ cross a b y) (hx : x ∈ interior s) : 0 < cross a b x := by
  by_contra hneg
  rw [not_lt] at hneg
  have hN : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := sq_add_sq_pos (sub_ne_zero.2 hab.symm)
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, x + δ • (-(nrm (b - a))) ∈ s :=
    (tendsto_add_smul x _).eventually (mem_interior_iff_mem_nhds.1 hx)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := eventually_mem_nhdsWithin
  obtain ⟨δ, hδs, hδ⟩ := (hev.and hpos).exists
  have h1 := hs _ hδs
  rw [cross_add_smul] at h1
  have e : det (b - a) (-(nrm (b - a))) = -((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    simp only [det, nrm, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
    ring
  rw [e] at h1
  nlinarith

/-! ### Area -/

/-- The open standard triangle is the region between `0` and `1 - x` over `(0, 1)`. -/
private theorem To_std : To (0 : ℝ × ℝ) (1, 0) (0, 1)
    = regionBetween (fun _ : ℝ => (0 : ℝ)) (fun x => 1 - x) (Ioo 0 1) := by
  ext ⟨x, y⟩
  simp only [To, cross, mem_ofPred_eq, regionBetween, mem_Ioo, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith⟩

/-- The open standard triangle has area `1/2`. -/
private theorem volume_To_std : volume (To (0 : ℝ × ℝ) (1, 0) (0, 1)) = ENNReal.ofReal (1 / 2) := by
  rw [To_std]
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (Ioo 0 1) volume := fun f hf =>
    (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have h := volume_regionBetween_eq_integral (μ := (volume : Measure ℝ))
    (f := fun _ : ℝ => (0 : ℝ)) (g := fun x => 1 - x) (s := Ioo 0 1)
    (hint _ continuous_const) (hint _ (continuous_const.sub continuous_id)) measurableSet_Ioo
    (fun x hx => by linarith [hx.2])
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, h]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [Pi.sub_apply, sub_zero]
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp
  norm_num

/-- The closed standard triangle has area `1/2`. -/
private theorem volume_std :
    volume (convexHull ℝ {(0 : ℝ × ℝ), (1, 0), (0, 1)}) = ENNReal.ofReal (1 / 2) := by
  have hD : 0 < det ((1, 0) - (0 : ℝ × ℝ)) ((0, 1) - 0) := by simp [det]
  have hint : interior (convexHull ℝ {(0 : ℝ × ℝ), (1, 0), (0, 1)}) = To 0 (1, 0) (0, 1) := by
    apply Subset.antisymm _ (To_subset_interior hD)
    intro x hx
    rw [Tc_eq_convexHull hD] at hx
    exact ⟨cross_pos_of_mem_interior (by simp [Prod.ext_iff]) (fun y hy => hy.1) hx,
      cross_pos_of_mem_interior (by simp [Prod.ext_iff]) (fun y hy => hy.2.1) hx,
      cross_pos_of_mem_interior (by simp [Prod.ext_iff]) (fun y hy => hy.2.2) hx⟩
  rw [← measure_interior_of_null_frontier ((convex_convexHull ℝ _).addHaar_frontier volume), hint,
    volume_To_std]

/-- The linear map of `ℝ²` with matrix columns `a`, `b`. -/
private def colMap (a b : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight a + (LinearMap.snd ℝ ℝ ℝ).smulRight b

private theorem colMap_apply (a b x : ℝ × ℝ) : colMap a b x = x.1 • a + x.2 • b := rfl

private theorem det_colMap (a b : ℝ × ℝ) : LinearMap.det (colMap a b) = det a b := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, colMap_apply, det]
  ring

/-- **Area of a triangle.**  The Lebesgue measure of the closed triangle with vertices `p, q, r`
is `|det (q - p, r - p)| / 2`. -/
theorem volume_triangle (p q r : ℝ × ℝ) :
    volume (convexHull ℝ {p, q, r}) = ENNReal.ofReal (|det (q - p) (r - p)| / 2) := by
  have himg : convexHull ℝ {p, q, r}
      = p +ᵥ (colMap (q - p) (r - p) '' convexHull ℝ {(0 : ℝ × ℝ), (1, 0), (0, 1)}) := by
    rw [LinearMap.image_convexHull, ← convexHull_vadd]
    congr 1
    simp [image_insert_eq, colMap_apply, vadd_set_insert]
  rw [himg, measure_vadd, Measure.addHaar_image_linearMap, volume_std,
    det_colMap, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- **Additivity.**  For countably many closed convex sets with pairwise disjoint interiors, the
measure of the union is the sum of the measures. -/
theorem volume_iUnion_of_disjoint_interiors {ι : Type*} [Countable ι] (T : ι → Set (ℝ × ℝ))
    (hconv : ∀ i, Convex ℝ (T i)) (hcl : ∀ i, IsClosed (T i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (T i)) (interior (T j))) :
    volume (⋃ i, T i) = ∑' i, volume (T i) := by
  apply measure_iUnion₀
  · intro i j hij
    have hsub : T i ∩ T j ⊆ frontier (T i) ∪ frontier (T j) := by
      rintro x ⟨hxi, hxj⟩
      by_cases h1 : x ∈ interior (T i)
      · by_cases h2 : x ∈ interior (T j)
        · exact absurd h2 (disjoint_left.1 (hdisj i j hij) h1)
        · exact Or.inr ⟨subset_closure hxj, h2⟩
      · exact Or.inl ⟨subset_closure hxi, h1⟩
    apply measure_mono_null hsub
    rw [measure_union_null_iff]
    exact ⟨(hconv i).addHaar_frontier volume, (hconv j).addHaar_frontier volume⟩
  · intro i
    exact (hcl i).measurableSet.nullMeasurableSet

end

end Stein
