import Stein.Basic

/-!
# The winding number of a closed polygonal curve, and simple closed polygons

A closed polygonal curve is given by its vertices `v : ι → ℝ × ℝ` (`ι` a finite type) and the
"next vertex" permutation `σ : ι ≃ ι`; its sides are the segments `v i → v (σ i)`.

* `ang a b x` : the signed angle in `(-π, π]` under which the oriented segment `a → b` is seen from
  `x` (the argument of `(b - x) / (a - x)`, points of the plane read as complex numbers).
* `angSum v σ x` : the sum of these angles over all sides.
* `wind v σ x : ℤ` : the winding number, `angSum / 2π` (it is an integer if `x` is not a vertex:
  `angSum_eq`).
* `wind_eventually_eq` : the winding number is locally constant off the curve.
* `wind_jump` : crossing a side from its right to its left increases the winding number by `1`.
* `Simple` : the curve is a simple closed polygon.
* `wind_side_const`, `wind_side_next`, `wind_side_all` : on the sides (end points removed) the
  winding number is one and the same number `l`.
* `wind_side_value`, `wind_side_cases` : `l = 1` or `l = 0`, according to the turn at the
  lexicographically smallest vertex.
* `curveCyc v σ`, `regionCyc v σ` : the curve, and the closed region bounded by it (the curve
  together with the points of non-zero winding number).
* `region_off`, `region_side`, `Simple.inter_finite` : the three properties which make up
  `Stein.OrientedBoundary` for the region of a simple closed polygon (for the sides `v i → v (σ i)`
  or for the reversed sides); `region_left_of_turn` decides which of the two cases holds.

Here `cross a b x` is `Stein.cross` (`Stein/Basic.lean`): it is positive iff `x` is strictly on the
left of the oriented line `a → b`.  The polygons `v : Fin (m + 3) → ℝ × ℝ` of the main theorem are
the special case `σ = finRotate (m + 3)`, see `Stein/Polygon/Region.lean`.
-/

open Set Filter Topology

namespace Stein.Polygon

noncomputable section

open Complex

/-! ### Points as complex numbers, the angle function -/

/-- a point of the plane as a complex number -/
def toC (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

/-- the real part of `toC p` is the first coordinate of `p` -/
@[simp] theorem toC_re (p : ℝ × ℝ) : (toC p).re = p.1 := by simp [toC]

/-- the imaginary part of `toC p` is the second coordinate of `p` -/
@[simp] theorem toC_im (p : ℝ × ℝ) : (toC p).im = p.2 := by simp [toC]

/-- `toC` is continuous -/
theorem continuous_toC : Continuous toC := by unfold toC; fun_prop

/-- `toC` is injective -/
theorem toC_inj {p q : ℝ × ℝ} : toC p = toC q ↔ p = q := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [toC_re, toC_im] at h1 h2
    exact Prod.ext h1 h2
  · rintro rfl; rfl

/-- different points have different images under `toC` -/
theorem toC_sub_ne {p q : ℝ × ℝ} (h : p ≠ q) : toC p - toC q ≠ 0 :=
  fun h0 => h (toC_inj.1 (sub_eq_zero.1 h0))

/-- the point `a + t (b - a)` of the line `a b` -/
def pt (a b : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := a + t • (b - a)

/-- `pt a b t` as a complex number -/
theorem toC_pt (a b : ℝ × ℝ) (t : ℝ) : toC (pt a b t) = toC a + t * (toC b - toC a) := by
  apply Complex.ext <;> simp [pt]

/-- `t ↦ pt a b t` is continuous -/
theorem continuous_pt (a b : ℝ × ℝ) : Continuous (pt a b) := by unfold pt; fun_prop

/-- `pt a b 0 = a` -/
@[simp] theorem pt_zero (a b : ℝ × ℝ) : pt a b 0 = a := by simp [pt]

/-- `pt a b 1 = b` -/
@[simp] theorem pt_one (a b : ℝ × ℝ) : pt a b 1 = b := by simp [pt]

/-- the open segment `a b` is the image of `(0, 1)` under `pt a b` -/
theorem openSegment_eq_pt (a b : ℝ × ℝ) : openSegment ℝ a b = pt a b '' Ioo 0 1 :=
  openSegment_eq_image' ℝ a b

/-- the segment `a b` is the image of `[0, 1]` under `pt a b` -/
theorem segment_eq_pt (a b : ℝ × ℝ) : segment ℝ a b = pt a b '' Icc 0 1 :=
  segment_eq_image' ℝ a b

/-- `pt a b t` is a point of the segment `a b` for `0 ≤ t ≤ 1` -/
theorem pt_mem_segment (a b : ℝ × ℝ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    pt a b t ∈ segment ℝ a b := by
  rw [segment_eq_pt]; exact ⟨t, ⟨h0, h1⟩, rfl⟩

/-- `pt a b t ≠ a` for `t ≠ 0` (and `a ≠ b`) -/
theorem pt_ne_left {a b : ℝ × ℝ} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 0) : pt a b t ≠ a := by
  intro h
  apply toC_sub_ne hab.symm
  have h1 := toC_pt a b t
  rw [h] at h1
  have h2 : (t : ℂ) * (toC b - toC a) = 0 := by linear_combination -h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast h3) ht
  · exact h3

/-- `pt a b t ≠ b` for `t ≠ 1` (and `a ≠ b`) -/
theorem pt_ne_right {a b : ℝ × ℝ} (hab : a ≠ b) {t : ℝ} (ht : t ≠ 1) : pt a b t ≠ b := by
  intro h
  apply toC_sub_ne hab.symm
  have h1 := toC_pt a b t
  rw [h] at h1
  have h2 : ((1 : ℂ) - t) * (toC b - toC a) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    apply ht
    have : ((1 - t : ℝ) : ℂ) = 0 := by push_cast; exact h3
    have h4 : 1 - t = 0 := by exact_mod_cast this
    linarith
  · exact h3

/-- the quotient `(b - x) / (a - x)` -/
def zq (a b x : ℝ × ℝ) : ℂ := (toC b - toC x) / (toC a - toC x)

/-- the signed angle under which the oriented segment `a → b` is seen from `x` -/
def ang (a b x : ℝ × ℝ) : ℝ := arg (zq a b x)

/-- the quotient `zq a b x` is not zero if `x` is neither `a` nor `b` -/
theorem zq_ne_zero {a b x : ℝ × ℝ} (ha : x ≠ a) (hb : x ≠ b) : zq a b x ≠ 0 :=
  div_ne_zero (toC_sub_ne hb.symm) (toC_sub_ne ha.symm)

/-- the imaginary part of `zq a b x` is `cross a b x` divided by `|a - x|²` -/
theorem zq_im (a b x : ℝ × ℝ) :
    (zq a b x).im = cross a b x / normSq (toC a - toC x) := by
  simp only [zq, Complex.div_im, cross, Complex.sub_re, Complex.sub_im, toC_re, toC_im]
  ring

/-- the real part of `zq a b x` is the scalar product of `b - x` and `a - x` divided by
`|a - x|²` -/
theorem zq_re (a b x : ℝ × ℝ) :
    (zq a b x).re = ((b.1 - x.1) * (a.1 - x.1) + (b.2 - x.2) * (a.2 - x.2)) /
      normSq (toC a - toC x) := by
  simp only [zq, Complex.div_re, Complex.sub_re, Complex.sub_im, toC_re, toC_im]
  ring

private theorem normSq_pos' {a x : ℝ × ℝ} (ha : x ≠ a) : 0 < normSq (toC a - toC x) :=
  normSq_pos.2 (toC_sub_ne ha.symm)

/-- strictly on the left of the line `a → b` the quotient `zq a b x` has positive imaginary part -/
theorem zq_im_pos {a b x : ℝ × ℝ} (ha : x ≠ a) (h : 0 < cross a b x) : 0 < (zq a b x).im := by
  rw [zq_im]; exact div_pos h (normSq_pos' ha)

/-- strictly on the right of the line `a → b` the quotient `zq a b x` has negative imaginary
part -/
theorem zq_im_neg {a b x : ℝ × ℝ} (ha : x ≠ a) (h : cross a b x < 0) : (zq a b x).im < 0 := by
  rw [zq_im]; exact div_neg_of_neg_of_pos h (normSq_pos' ha)

/-- off the segment `a b` the quotient is not a real number `≤ 0` -/
theorem zq_mem_slitPlane {a b x : ℝ × ℝ} (hx : x ∉ segment ℝ a b) : zq a b x ∈ slitPlane := by
  have ha : x ≠ a := fun h => hx (h ▸ left_mem_segment ℝ a b)
  by_contra hn
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hn
  obtain ⟨hre, him⟩ := hn
  have hN := normSq_pos' ha
  rw [zq_re] at hre
  rw [zq_im] at him
  have hC : cross a b x = 0 := by
    rcases div_eq_zero_iff.1 him with h | h
    · exact h
    · exact absurd h hN.ne'
  set D := (b.1 - x.1) * (a.1 - x.1) + (b.2 - x.2) * (a.2 - x.2) with hD
  have hD0 : D ≤ 0 := by
    by_contra h
    exact absurd hre (not_le.2 (div_pos (not_le.1 h) hN))
  set N := normSq (toC a - toC x) with hNdef
  have hNe : N = (a.1 - x.1) ^ 2 + (a.2 - x.2) ^ 2 := by
    simp only [hNdef, normSq_apply, Complex.sub_re, Complex.sub_im, toC_re, toC_im]; ring
  have hpos : 0 < N - D := by linarith
  apply hx
  refine ⟨-D / (N - D), N / (N - D), div_nonneg (by linarith) hpos.le, div_nonneg hN.le hpos.le,
    ?_, ?_⟩
  · rw [← add_div, div_eq_one_iff_eq hpos.ne']; ring
  · unfold cross at hC
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hpos.ne', hNe, hD]
      linear_combination -(a.2 - x.2) * hC
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hpos.ne', hNe, hD]
      linear_combination (a.1 - x.1) * hC

/-- the quotient `zq a b x` is a continuous function of `x ≠ a` -/
theorem continuousAt_zq {a b x : ℝ × ℝ} (ha : x ≠ a) : ContinuousAt (zq a b) x := by
  unfold zq
  exact ((continuous_const.sub continuous_toC).continuousAt).div
    ((continuous_const.sub continuous_toC).continuousAt) (toC_sub_ne ha.symm)

/-- off the segment `a b` the angle is continuous -/
theorem continuousAt_ang {a b x : ℝ × ℝ} (hx : x ∉ segment ℝ a b) : ContinuousAt (ang a b) x := by
  have ha : x ≠ a := fun h => hx (h ▸ left_mem_segment ℝ a b)
  exact (continuousAt_arg (zq_mem_slitPlane hx)).comp (continuousAt_zq ha)

/-- on the open segment the quotient is a negative real number -/
theorem zq_pt {a b : ℝ × ℝ} (hab : a ≠ b) {t : ℝ} (h0 : 0 < t) :
    zq a b (pt a b t) = ((-(1 - t) / t : ℝ) : ℂ) := by
  have hne := toC_sub_ne hab.symm
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  unfold zq
  rw [toC_pt]
  have e1 : toC b - (toC a + t * (toC b - toC a)) = (1 - t) * (toC b - toC a) := by ring
  have e2 : toC a - (toC a + t * (toC b - toC a)) = -t * (toC b - toC a) := by ring
  rw [e1, e2]
  push_cast
  field_simp

/-- from a point of the open segment `a b`, the segment is seen under the angle `π` -/
theorem ang_pt {a b : ℝ × ℝ} (hab : a ≠ b) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ang a b (pt a b t) = Real.pi := by
  unfold ang
  rw [zq_pt hab h0]
  exact arg_ofReal_of_neg (div_neg_of_neg_of_pos (by linarith) h0)

/-- `arg (z / w) = arg z - arg w` if the right-hand side is in `(-π, π]` -/
theorem arg_div_eq {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h : arg z - arg w ∈ Ioc (-Real.pi) Real.pi) : arg (z / w) = arg z - arg w := by
  have hr : 0 < ‖z‖ / ‖w‖ := div_pos (norm_pos_iff.2 hz) (norm_pos_iff.2 hw)
  have key : z / w = ((‖z‖ / ‖w‖ : ℝ) : ℂ) *
      (Complex.cos ((arg z - arg w : ℝ) : ℂ) + Complex.sin ((arg z - arg w : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_mul_I]
    have e1 := norm_mul_exp_arg_mul_I z
    have e2 := norm_mul_exp_arg_mul_I w
    have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw).ne'
    have e3 : Complex.exp (((arg z - arg w : ℝ) : ℂ) * I) =
        Complex.exp (arg z * I) / Complex.exp (arg w * I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    rw [e3]
    conv_lhs => rw [← e1, ← e2]
    push_cast
    field_simp
  rw [key]
  exact arg_mul_cos_add_sin_mul_I hr h

/-! ### The winding number -/

variable {ι : Type*} [Fintype ι]

/-- the sum of the angles under which the sides `v i → v (σ i)` are seen from `x` -/
def angSum (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (x : ℝ × ℝ) : ℝ := ∑ i, ang (v i) (v (σ i)) x

/-- the winding number of the closed polygonal curve around `x` -/
def wind (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (x : ℝ × ℝ) : ℤ := round (angSum v σ x / (2 * Real.pi))

/-- if `x` is not a vertex, the angle sum is `2π` times the winding number -/
theorem angSum_eq (v : ι → ℝ × ℝ) (σ : ι ≃ ι) {x : ℝ × ℝ} (hx : ∀ i, x ≠ v i) :
    angSum v σ x = 2 * Real.pi * wind v σ x := by
  have hz : ∀ i, zq (v i) (v (σ i)) x ≠ 0 := fun i => zq_ne_zero (hx i) (hx (σ i))
  have hprod : ∏ i, zq (v i) (v (σ i)) x = 1 := by
    unfold zq
    rw [Finset.prod_div_distrib, Equiv.prod_comp σ (fun i => toC (v i) - toC x)]
    exact div_self (Finset.prod_ne_zero_iff.2 (fun i _ => toC_sub_ne (hx i).symm))
  have hnorm : ∏ i, (‖zq (v i) (v (σ i)) x‖ : ℂ) = 1 := by
    rw [← Complex.ofReal_prod, ← norm_prod, hprod, norm_one, Complex.ofReal_one]
  have hexp : Complex.exp ((angSum v σ x : ℝ) * I) = 1 := by
    unfold angSum
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    have e : ∀ i, Complex.exp ((ang (v i) (v (σ i)) x : ℝ) * I) =
        zq (v i) (v (σ i)) x / (‖zq (v i) (v (σ i)) x‖ : ℂ) := by
      intro i
      have hn : (‖zq (v i) (v (σ i)) x‖ : ℂ) ≠ 0 := by
        exact_mod_cast (norm_pos_iff.2 (hz i)).ne'
      rw [eq_div_iff hn, mul_comm]
      exact norm_mul_exp_arg_mul_I _
    simp only [e]
    rw [Finset.prod_div_distrib, hprod, hnorm, div_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  have hn' : angSum v σ x = n * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simpa using h
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  unfold wind
  rw [hn', mul_div_assoc, div_self hpi, mul_one, round_intCast]
  ring

/-- two integers `m, n` with `|2π m - 2π n| < 2π` are equal -/
private theorem int_eq_of_close {m n : ℤ}
    (h : |2 * Real.pi * (m : ℝ) - 2 * Real.pi * n| < 2 * Real.pi) : m = n := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [← mul_sub, abs_mul, abs_of_pos hpi] at h
  have h1 : |((m - n : ℤ) : ℝ)| < 1 := by
    push_cast
    by_contra hc
    nlinarith [not_lt.1 hc]
  have h2 : |m - n| < 1 := by exact_mod_cast h1
  have := Int.abs_lt_one_iff.1 h2
  omega

/-- the points near a non-vertex are not vertices -/
private theorem eventually_ne_vertex (v : ι → ℝ × ℝ) {x : ℝ × ℝ} (hx : ∀ i, x ≠ v i) :
    ∀ᶠ y in 𝓝 x, ∀ i, y ≠ v i :=
  eventually_all.2 (fun i => isOpen_ne.mem_nhds (hx i))

/-- **the winding number is locally constant off the curve** -/
theorem wind_eventually_eq (v : ι → ℝ × ℝ) (σ : ι ≃ ι) {x : ℝ × ℝ}
    (hx : ∀ i, x ∉ segment ℝ (v i) (v (σ i))) : ∀ᶠ y in 𝓝 x, wind v σ y = wind v σ x := by
  have hxv : ∀ i, x ≠ v i := fun i h => hx i (h ▸ left_mem_segment ℝ _ _)
  have hc : Tendsto (angSum v σ) (𝓝 x) (𝓝 (angSum v σ x)) :=
    tendsto_finsetSum _ (fun i _ => continuousAt_ang (hx i))
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := hc.eventually (Metric.ball_mem_nhds _ hpi)
  filter_upwards [h1, eventually_ne_vertex v hxv] with y hy hyv
  apply int_eq_of_close
  rw [← angSum_eq v σ hyv, ← angSum_eq v σ hxv]
  exact hy

/-- **crossing a side from the right to the left increases the winding number by one**; a point
of the side itself counts with the left side.  Here `x` is a point of the side `k`, not an end
point, and on no other side. -/
theorem wind_jump (v : ι → ℝ × ℝ) (σ : ι ≃ ι) (k : ι) (hab : v k ≠ v (σ k)) {t : ℝ}
    (h0 : 0 < t) (h1 : t < 1)
    (hx : ∀ j, j ≠ k → pt (v k) (v (σ k)) t ∉ segment ℝ (v j) (v (σ j))) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → wind v σ y = wind v σ (pt (v k) (v (σ k)) t)) ∧
      (cross (v k) (v (σ k)) y < 0 → wind v σ y = wind v σ (pt (v k) (v (σ k)) t) - 1) := by
  classical
  set a := v k with ha
  set b := v (σ k) with hb
  set x := pt a b t with hxdef
  have hxv : ∀ i, x ≠ v i := by
    intro i
    by_cases hik : i = k
    · rw [hik]; exact pt_ne_left hab h0.ne'
    · exact fun h => hx i hik (h ▸ left_mem_segment ℝ _ _)
  set F : (ℝ × ℝ) → ℝ := fun y => ∑ j ∈ Finset.univ.erase k, ang (v j) (v (σ j)) y with hF
  have hsplit : ∀ y, angSum v σ y = ang a b y + F y := fun y =>
    (Finset.add_sum_erase Finset.univ (fun j => ang (v j) (v (σ j)) y) (Finset.mem_univ k)).symm
  have hFc : ContinuousAt F x :=
    tendsto_finsetSum _ (fun j hj => continuousAt_ang (hx j (Finset.ne_of_mem_erase hj)))
  have hr : 0 < (1 - t) / t := div_pos (by linarith) h0
  have hzx : -(zq a b x) = (((1 - t) / t : ℝ) : ℂ) := by
    rw [hxdef, zq_pt hab h0]; push_cast; ring
  have hslit : -(zq a b x) ∈ slitPlane := by
    rw [hzx, mem_slitPlane_iff]; left; rw [Complex.ofReal_re]; exact hr
  have hAc : ContinuousAt (fun y => arg (-(zq a b y))) x :=
    ContinuousAt.comp (f := fun y => -(zq a b y)) (g := arg) (continuousAt_arg hslit)
      (continuousAt_zq (hxv k)).neg
  have hHc : ContinuousAt (fun y => F y + arg (-(zq a b y))) x := hFc.add hAc
  have hAx : arg (-(zq a b x)) = 0 := by rw [hzx]; exact arg_ofReal_of_nonneg hr.le
  have hSx : angSum v σ x = Real.pi + F x := by rw [hsplit, hxdef, ang_pt hab h0 h1]
  have hpi := Real.pi_pos
  have h1' := hHc.eventually (Metric.ball_mem_nhds _ hpi)
  filter_upwards [h1', eventually_ne_vertex v hxv] with y hy hyv
  rw [Real.dist_eq, hAx, add_zero] at hy
  have hSy := hsplit y
  have ey := angSum_eq v σ hyv
  have ex := angSum_eq v σ hxv
  have hy' := abs_lt.1 hy
  constructor
  · intro hc
    have hA := arg_neg_eq_arg_sub_pi_of_im_pos (zq_im_pos (hyv k) hc)
    apply int_eq_of_close
    rw [← ey, ← ex, hSy, hSx, abs_lt]
    unfold ang
    constructor <;> linarith [hy'.1, hy'.2]
  · intro hc
    have hA := arg_neg_eq_arg_add_pi_of_im_neg (zq_im_neg (hyv k) hc)
    apply int_eq_of_close
    push_cast
    rw [mul_sub, ← ey, ← ex, hSy, hSx, abs_lt]
    unfold ang
    constructor <;> linarith [hy'.1, hy'.2]

/-! ### Simple closed polygons -/

/-- The closed polygonal curve with vertices `v i` and sides `v i → v (σ i)` is a **simple closed
polygon**: consecutive vertices are different, two different sides have no common point except
that consecutive sides share their common vertex (and only it), and `σ` is one cycle. -/
structure Simple (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : Prop where
  ne : ∀ i, v i ≠ v (σ i)
  meet : ∀ i j, i ≠ j → ∀ x, x ∈ segment ℝ (v i) (v (σ i)) → x ∈ segment ℝ (v j) (v (σ j)) →
    (j = σ i ∧ x = v j) ∨ (i = σ j ∧ x = v i)
  cyc : ∃ i₀, ∀ P : ι → Prop, P i₀ → (∀ i, P i → P (σ i)) → ∀ j, P j

variable {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

omit [Fintype ι] in
/-- the vertices of a simple closed polygon are pairwise different -/
theorem Simple.inj (hs : Simple v σ) : Function.Injective v := by
  intro i j hij
  by_contra hne
  rcases hs.meet i j hne (v i) (left_mem_segment ℝ _ _) (hij ▸ left_mem_segment ℝ _ _) with
    ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hs.ne i (by rw [← h1]; exact hij)
  · exact hs.ne j (by rw [← h1]; exact hij.symm)

omit [Fintype ι] in
/-- the successor permutation of a simple closed polygon has no fixed point -/
theorem Simple.next_ne (hs : Simple v σ) (i : ι) : σ i ≠ i :=
  fun h => hs.ne i (by rw [h])

omit [Fintype ι] in
/-- a point of a side, not an end point, is on no other side -/
theorem Simple.pt_not_mem (hs : Simple v σ) (k : ι) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (j : ι)
    (hj : j ≠ k) : pt (v k) (v (σ k)) t ∉ segment ℝ (v j) (v (σ j)) := by
  intro hmem
  rcases hs.meet k j hj.symm _ (pt_mem_segment _ _ h0.le h1.le) hmem with ⟨h2, h3⟩ | ⟨_, h3⟩
  · rw [h2] at h3; exact pt_ne_right (hs.ne k) h1.ne h3
  · exact pt_ne_left (hs.ne k) h0.ne' h3

omit [Fintype ι] in
/-- a point of a side, not an end point, is not a vertex -/
theorem Simple.pt_ne_vertex (hs : Simple v σ) (k : ι) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (i : ι) :
    pt (v k) (v (σ k)) t ≠ v i := by
  by_cases hik : i = k
  · rw [hik]; exact pt_ne_left (hs.ne k) h0.ne'
  · exact fun h => hs.pt_not_mem k h0 h1 i hik (h ▸ left_mem_segment ℝ _ _)

/-- the winding number is constant on a side (end points removed) -/
theorem wind_side_const (hs : Simple v σ) (k : ι) {s t : ℝ} (hs' : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    wind v σ (pt (v k) (v (σ k)) s) = wind v σ (pt (v k) (v (σ k)) t) := by
  classical
  set a := v k with ha
  set b := v (σ k) with hb
  have hloc : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ t' in 𝓝 t, wind v σ (pt a b t') = wind v σ (pt a b t) := by
    intro t ht
    set F : (ℝ × ℝ) → ℝ := fun y => ∑ j ∈ Finset.univ.erase k, ang (v j) (v (σ j)) y with hF
    have hsplit : ∀ y, angSum v σ y = ang a b y + F y := fun y =>
      (Finset.add_sum_erase Finset.univ (fun j => ang (v j) (v (σ j)) y) (Finset.mem_univ k)).symm
    have hFc : ContinuousAt F (pt a b t) :=
      tendsto_finsetSum _ (fun j hj =>
        continuousAt_ang (hs.pt_not_mem k ht.1 ht.2 j (Finset.ne_of_mem_erase hj)))
    have hFc' : ContinuousAt (fun t' => F (pt a b t')) t :=
      ContinuousAt.comp (f := pt a b) (g := F) hFc (continuous_pt a b).continuousAt
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    filter_upwards [hFc'.eventually (Metric.ball_mem_nhds _ hpi), Ioo_mem_nhds ht.1 ht.2]
      with t' h1 h2
    apply int_eq_of_close
    rw [← angSum_eq v σ (hs.pt_ne_vertex k h2.1 h2.2),
      ← angSum_eq v σ (hs.pt_ne_vertex k ht.1 ht.2),
      hsplit, hsplit, ang_pt (hs.ne k) h2.1 h2.2, ang_pt (hs.ne k) ht.1 ht.2]
    rw [Real.dist_eq] at h1
    rw [add_sub_add_left_eq_sub]
    exact h1
  have hcont : ContinuousOn (fun t => wind v σ (pt a b t)) (Ioo (0 : ℝ) 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.congr (EventuallyEq.symm (hloc t ht))
  exact isPreconnected_Ioo.constant hcont hs' ht

/-- a function continuous at `0` and equal to `c` on `(0, 1)` takes the value `c` at `0` -/
private theorem eq_of_const_Ioo {g : ℝ → ℝ} {c : ℝ} (hc : ContinuousAt g 0)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, g t = c) : g 0 = c := by
  have h1 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    exact (h t ht).symm
  exact tendsto_nhds_unique h1 h2

/-- reversing the segment: `pt a b (1 - t) = pt b a t` -/
theorem pt_symm (a b : ℝ × ℝ) (t : ℝ) : pt a b (1 - t) = pt b a t := by
  apply toC_inj.1
  rw [toC_pt, toC_pt]; push_cast; ring

omit [Fintype ι] in
/-- at a vertex `p = v (σ i)` the next side does not go back along the previous one:
`(b - p) / (p - a)` is not a real number `≤ 0` -/
theorem Simple.turn_slit (hs : Simple v σ) (i : ι) :
    (toC (v (σ (σ i))) - toC (v (σ i))) / (toC (v (σ i)) - toC (v i)) ∈ slitPlane := by
  set a := v i with ha
  set p := v (σ i) with hp
  set b := v (σ (σ i)) with hb
  have hap : a ≠ p := hs.ne i
  have hpb : p ≠ b := hs.ne (σ i)
  by_contra hn
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hn
  obtain ⟨hre, him⟩ := hn
  set z := (toC b - toC p) / (toC p - toC a) with hz
  have hzr : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hne := toC_sub_ne hap.symm
  have e1 : toC b - toC p = (-z.re : ℝ) * (toC a - toC p) := by
    have : toC b - toC p = z * (toC p - toC a) := by rw [hz]; field_simp
    rw [this, hzr]; push_cast; simp only [Complex.ofReal_re]; ring
  set s := -z.re with hsdef
  have hs0 : 0 ≤ s := by linarith
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0] at e1
    apply toC_sub_ne hpb.symm
    rw [e1]; simp
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsne)
  -- the point `x = p + τ (a - p)` with `τ = min s 1 / 2` is on both sides
  set τ := min s 1 / 2 with hτ
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ < 1 := by
    have := min_le_right s 1
    rw [hτ]; linarith
  have hτs : τ < s := by
    have := min_le_left s 1
    rw [hτ]; linarith
  have hx1 : pt p a τ ∈ segment ℝ a p := by
    rw [segment_symm]; exact pt_mem_segment _ _ hτ0.le hτ1.le
  have hx2 : pt p a τ = pt p b (τ / s) := by
    apply toC_inj.1
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hsne
    rw [toC_pt, toC_pt, e1]
    push_cast
    field_simp
  have hx3 : pt p a τ ∈ segment ℝ p b := by
    rw [hx2]
    exact pt_mem_segment _ _ (div_nonneg hτ0.le hs0) ((div_le_one hspos).2 hτs.le)
  rcases hs.meet i (σ i) (hs.next_ne i).symm _ hx1 hx3 with ⟨_, h3⟩ | ⟨_, h3⟩
  · exact pt_ne_left hap.symm hτ0.ne' h3
  · exact pt_ne_right hap.symm hτ1.ne h3

/-- splitting off the terms `i` and `σ i` of a sum over all sides -/
private theorem sum_split3 [DecidableEq ι] (hs : Simple v σ) (i : ι) (f : ι → ℝ) :
    ∑ j, f j = f i + f (σ i) + ∑ j ∈ (Finset.univ.erase i).erase (σ i), f j := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) f
      (Finset.mem_erase.2 ⟨hs.next_ne i, Finset.mem_univ _⟩)]
  ring

/-- the sides other than the two sides at the vertex `v (σ i)` do not contain it -/
theorem Simple.vertex_not_mem [DecidableEq ι] (hs : Simple v σ) (i : ι) {j : ι}
    (hj : j ∈ (Finset.univ.erase i).erase (σ i)) : v (σ i) ∉ segment ℝ (v j) (v (σ j)) := by
  have hj1 : j ≠ σ i := Finset.ne_of_mem_erase hj
  have hj2 : j ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
  intro hmem
  rcases hs.meet i j hj2.symm _ (right_mem_segment ℝ _ _) hmem with ⟨h, _⟩ | ⟨_, h⟩
  · exact hj1 h
  · exact hs.ne i h.symm

/-- the angle sum of the sides other than the two sides at the vertex `v (σ i)` is continuous
at this vertex -/
private theorem Simple.continuousAt_rest [DecidableEq ι] (hs : Simple v σ) (i : ι) :
    ContinuousAt (fun y => ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) y)
      (v (σ i)) :=
  tendsto_finsetSum _ (fun _ hj => continuousAt_ang (hs.vertex_not_mem i hj))

/-- **vertex formula, outgoing side**: on the side leaving the vertex `p = v (σ i)`, `2π` times
the winding number is the angle sum of the other sides at `p`, plus `π`, plus the argument of
`(b - p) / (p - a)`. -/
theorem vertex_out [DecidableEq ι] (hs : Simple v σ) (i : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    2 * Real.pi * wind v σ (pt (v (σ i)) (v (σ (σ i))) t) =
      ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) (v (σ i)) + Real.pi +
        arg ((toC (v (σ (σ i))) - toC (v (σ i))) / (toC (v (σ i)) - toC (v i))) := by
  set a := v i with ha
  set p := v (σ i) with hp
  set b := v (σ (σ i)) with hb
  set G : (ℝ × ℝ) → ℝ := fun y => ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) y
    with hG
  have hGc : ContinuousAt G p := hs.continuousAt_rest i
  have hap : a ≠ p := hs.ne i
  have hne : toC a - toC p ≠ 0 := toC_sub_ne hap
  set u : ℝ → ℂ := fun t => -(toC b - toC p) / (toC a - toC p - t * (toC b - toC p)) with hu
  have hu0 : u 0 = (toC b - toC p) / (toC p - toC a) := by
    simp only [hu]
    rw [Complex.ofReal_zero, zero_mul, sub_zero, ← neg_sub (toC p) (toC a), neg_div_neg_eq]
  set g : ℝ → ℝ := fun t => G (pt p b t) + Real.pi + arg (u t) with hg
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t => G (pt p b t)) 0 := by
      apply ContinuousAt.comp (f := pt p b) (g := G) _ (continuous_pt p b).continuousAt
      rw [pt_zero]; exact hGc
    have h2 : ContinuousAt u 0 := by
      apply ContinuousAt.div
      · exact continuousAt_const
      · fun_prop
      · rw [Complex.ofReal_zero, zero_mul, sub_zero]; exact hne
    have h3 : ContinuousAt (fun t => arg (u t)) 0 := by
      apply ContinuousAt.comp (f := u) (g := arg) _ h2
      apply continuousAt_arg
      rw [hu0]; exact hs.turn_slit i
    exact (h1.add continuousAt_const).add h3
  have hval : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 2 * Real.pi * wind v σ (pt p b t) := by
    intro t ht
    have hyv := hs.pt_ne_vertex (σ i) ht.1 ht.2
    rw [← angSum_eq v σ hyv]
    unfold angSum
    rw [sum_split3 hs i, ang_pt (hs.ne (σ i)) ht.1 ht.2]
    have e : zq a p (pt p b t) = (t : ℂ) * u t := by
      simp only [zq, hu]
      rw [toC_pt]
      have hden : toC a - (toC p + t * (toC b - toC p)) ≠ 0 := by
        rw [← toC_pt]; exact toC_sub_ne (hyv i).symm
      have hden' : toC a - toC p - t * (toC b - toC p) ≠ 0 := by
        rw [sub_sub]; exact hden
      field_simp
      ring
    have e2 : ang a p (pt p b t) = arg (u t) := by
      unfold ang
      rw [e, arg_real_mul _ ht.1]
    rw [e2]
    simp only [hg, hG]
    ring
  have hconst : ∀ t' ∈ Ioo (0 : ℝ) 1, g t' = 2 * Real.pi * wind v σ (pt p b t) := by
    intro t' ht'
    rw [hval t' ht', wind_side_const hs (σ i) ht' ht]
  have h0 := eq_of_const_Ioo hgc hconst
  rw [← h0]
  simp only [hg, hG]
  rw [pt_zero, hu0]

/-- **vertex formula, incoming side** -/
theorem vertex_in [DecidableEq ι] (hs : Simple v σ) (i : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    2 * Real.pi * wind v σ (pt (v i) (v (σ i)) t) =
      ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) (v (σ i)) + Real.pi +
        arg ((toC (v (σ (σ i))) - toC (v (σ i))) / (toC (v (σ i)) - toC (v i))) := by
  set a := v i with ha
  set p := v (σ i) with hp
  set b := v (σ (σ i)) with hb
  set G : (ℝ × ℝ) → ℝ := fun y => ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) y
    with hG
  have hGc : ContinuousAt G p := hs.continuousAt_rest i
  have hap : a ≠ p := hs.ne i
  have hne : toC p - toC a ≠ 0 := toC_sub_ne hap.symm
  set u : ℝ → ℂ := fun t => (toC b - toC p - t * (toC a - toC p)) / (toC p - toC a) with hu
  have hu0 : u 0 = (toC b - toC p) / (toC p - toC a) := by
    simp only [hu]
    rw [Complex.ofReal_zero, zero_mul, sub_zero]
  set g : ℝ → ℝ := fun t => G (pt p a t) + Real.pi + arg (u t) with hg
  have hgc : ContinuousAt g 0 := by
    have h1 : ContinuousAt (fun t => G (pt p a t)) 0 := by
      apply ContinuousAt.comp (f := pt p a) (g := G) _ (continuous_pt p a).continuousAt
      rw [pt_zero]; exact hGc
    have h2 : ContinuousAt u 0 := by
      apply ContinuousAt.div
      · fun_prop
      · exact continuousAt_const
      · exact hne
    have h3 : ContinuousAt (fun t => arg (u t)) 0 := by
      apply ContinuousAt.comp (f := u) (g := arg) _ h2
      apply continuousAt_arg
      rw [hu0]; exact hs.turn_slit i
    exact (h1.add continuousAt_const).add h3
  have hval : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 2 * Real.pi * wind v σ (pt p a t) := by
    intro t ht
    have ht' : (0 : ℝ) < 1 - t ∧ 1 - t < 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hy : pt p a t = pt a p (1 - t) := (pt_symm a p t).symm
    have hyv : ∀ j, pt p a t ≠ v j := by
      rw [hy]; exact hs.pt_ne_vertex i ht'.1 ht'.2
    rw [← angSum_eq v σ hyv]
    unfold angSum
    rw [sum_split3 hs i]
    have e1 : ang a p (pt p a t) = Real.pi := by
      rw [hy]; exact ang_pt (hs.ne i) ht'.1 ht'.2
    have e : zq p b (pt p a t) = ((t⁻¹ : ℝ) : ℂ) * u t := by
      simp only [zq, hu]
      rw [toC_pt]
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
      have hne' : toC a - toC p ≠ 0 := toC_sub_ne hap
      have e3 : toC p - (toC p + t * (toC a - toC p)) = -(t * (toC a - toC p)) := by ring
      have e4 : toC p - toC a = -(toC a - toC p) := by ring
      rw [e3, e4]
      push_cast
      field_simp
      ring
    have e2 : ang p b (pt p a t) = arg (u t) := by
      unfold ang
      rw [e, arg_real_mul _ (inv_pos.2 ht.1)]
    rw [e1, e2]
    simp only [hg, hG]
    ring
  have ht1 : (0 : ℝ) < 1 - t ∧ 1 - t < 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hconst : ∀ t' ∈ Ioo (0 : ℝ) 1, g t' = 2 * Real.pi * wind v σ (pt a p t) := by
    intro t' ht'
    have ht'' : (1 - t') ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
    rw [hval t' ht', ← pt_symm a p t', wind_side_const hs i ht'' ht]
  have h0 := eq_of_const_Ioo hgc hconst
  rw [← h0]
  simp only [hg, hG]
  rw [pt_zero, hu0]

/-- the winding number on a side equals the winding number on the next side -/
theorem wind_side_next (hs : Simple v σ) (i : ι) {s t : ℝ} (hs' : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    wind v σ (pt (v i) (v (σ i)) s) = wind v σ (pt (v (σ i)) (v (σ (σ i))) t) := by
  classical
  apply int_eq_of_close
  rw [vertex_in hs i hs', vertex_out hs i ht, sub_self, abs_zero]
  positivity

/-- **on all sides of a simple closed polygon (end points removed) the winding number is the
same number** -/
theorem wind_side_all (hs : Simple v σ) :
    ∃ l : ℤ, ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = l := by
  obtain ⟨i₀, hcyc⟩ := hs.cyc
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨wind v σ (pt (v i₀) (v (σ i₀)) (1 / 2)), ?_⟩
  apply hcyc
  · intro t ht
    exact wind_side_const hs i₀ ht hhalf
  · intro i hi t ht
    rw [← wind_side_next hs i hhalf ht]
    exact hi _ hhalf

/-- **the common value is `1` or `0`**, according to the turn at a lexicographically smallest
vertex `p = v (σ i)`: left turn (counter-clockwise polygon) gives `1`, right turn gives `0`;
there is no third case. -/
theorem wind_side_value (hs : Simple v σ) (i : ι)
    (hmin : ∀ j, (v (σ i)).1 ≤ (v j).1 ∧ ((v (σ i)).1 = (v j).1 → (v (σ i)).2 ≤ (v j).2))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    cross (v i) (v (σ i)) (v (σ (σ i))) ≠ 0 ∧
    (0 < cross (v i) (v (σ i)) (v (σ (σ i))) →
      wind v σ (pt (v (σ i)) (v (σ (σ i))) t) = 1) ∧
    (cross (v i) (v (σ i)) (v (σ (σ i))) < 0 →
      wind v σ (pt (v (σ i)) (v (σ (σ i))) t) = 0) := by
  classical
  have hvo := vertex_out hs i ht
  set a := v i with ha
  set p := v (σ i) with hp
  set b := v (σ (σ i)) with hb
  have hpa : p ≠ a := (hs.ne i).symm
  have hpb : p ≠ b := hs.ne (σ i)
  have hpi := Real.pi_pos
  set φ : (ℝ × ℝ) → ℝ := fun q => arg (toC q - toC p) with hφdef
  have hφ : ∀ j, v j ≠ p → -(Real.pi / 2) < φ (v j) ∧ φ (v j) ≤ Real.pi / 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hmin j
    have hre : (toC (v j) - toC p).re = (v j).1 - p.1 := by simp
    have him : (toC (v j) - toC p).im = (v j).2 - p.2 := by simp
    constructor
    · apply neg_pi_div_two_lt_arg_iff.2
      rw [hre, him]
      by_cases h : p.1 < (v j).1
      · left; linarith
      · right
        have := h2 (le_antisymm h1 (not_lt.1 h))
        linarith
    · apply arg_le_pi_div_two_iff.2
      left; rw [hre]; linarith
  have hang : ∀ j ∈ (Finset.univ.erase i).erase (σ i),
      ang (v j) (v (σ j)) p = φ (v (σ j)) - φ (v j) := by
    intro j hj
    have hj1 : j ≠ σ i := Finset.ne_of_mem_erase hj
    have hj2 : j ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    have n1 : v j ≠ p := hs.inj.ne hj1
    have n2 : v (σ j) ≠ p := hs.inj.ne (σ.injective.ne hj2)
    obtain ⟨l1, u1⟩ := hφ j n1
    obtain ⟨l2, u2⟩ := hφ (σ j) n2
    unfold ang zq
    exact arg_div_eq (toC_sub_ne n2) (toC_sub_ne n1) ⟨by simp only [hφdef] at *; linarith,
      by simp only [hφdef] at *; linarith⟩
  have hsum : ∑ j ∈ (Finset.univ.erase i).erase (σ i), ang (v j) (v (σ j)) p = φ a - φ b := by
    rw [Finset.sum_congr rfl hang]
    have h3 := sum_split3 hs i (fun j => φ (v (σ j)) - φ (v j))
    have h0 : ∑ j, (φ (v (σ j)) - φ (v j)) = 0 := by
      rw [Finset.sum_sub_distrib, Equiv.sum_comp σ (fun j => φ (v j)), sub_self]
    rw [h0] at h3
    simp only [← ha, ← hp, ← hb] at h3
    linarith
  rw [hsum] at hvo
  set w := zq a b p with hw
  have hwe : (toC b - toC p) / (toC p - toC a) = -w := by
    rw [hw, zq, ← neg_sub (toC a) (toC p), div_neg]
  have hslit := hs.turn_slit i
  rw [← ha, ← hp, ← hb, hwe] at hslit
  rw [hwe] at hvo
  obtain ⟨la, ua⟩ := hφ i hpa.symm
  obtain ⟨lb, ub⟩ := hφ (σ (σ i)) hpb.symm
  rw [← ha] at la ua
  rw [← hb] at lb ub
  have hargw : arg w = φ b - φ a := by
    rw [hw, zq]
    exact arg_div_eq (toC_sub_ne hpb.symm) (toC_sub_ne hpa.symm)
      ⟨by simp only [hφdef] at *; linarith, by simp only [hφdef] at *; linarith⟩
  have him : w.im ≠ 0 := by
    intro h0
    rw [mem_slitPlane_iff] at hslit
    rcases hslit with h | h
    · have hre : w.re < 0 := by
        rw [Complex.neg_re] at h; linarith
      have := arg_eq_pi_iff.2 ⟨hre, h0⟩
      rw [hargw] at this
      linarith
    · apply h; rw [Complex.neg_im, h0, neg_zero]
  have hcr : cross a b p = -cross a p b := by unfold cross; ring
  have himw : w.im = cross a b p / normSq (toC a - toC p) := zq_im a b p
  have hN := normSq_pos' hpa
  have hcne : cross a p b ≠ 0 := by
    intro h0
    apply him
    rw [himw, hcr, h0, neg_zero, zero_div]
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  refine ⟨hcne, ?_, ?_⟩
  · intro hc
    have hneg : w.im < 0 := by
      rw [himw]; exact div_neg_of_neg_of_pos (by linarith) hN
    have hA := arg_neg_eq_arg_add_pi_of_im_neg hneg
    have h1 : (2 * Real.pi) * (wind v σ (pt p b t) : ℝ) = 2 * Real.pi * ((1 : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ h2pi h1
  · intro hc
    have hpos : 0 < w.im := by
      rw [himw]; exact div_pos (by linarith) hN
    have hA := arg_neg_eq_arg_sub_pi_of_im_pos hpos
    have h1 : (2 * Real.pi) * (wind v σ (pt p b t) : ℝ) = 2 * Real.pi * ((0 : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast mul_left_cancel₀ h2pi h1

omit [Fintype ι] in
/-- a simple closed polygon has a lexicographically smallest vertex -/
private theorem Simple.exists_lexmin [Finite ι] (hs : Simple v σ) :
    ∃ i, ∀ j, (v (σ i)).1 ≤ (v j).1 ∧ ((v (σ i)).1 = (v j).1 → (v (σ i)).2 ≤ (v j).2) := by
  obtain ⟨i₀, _⟩ := hs.cyc
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨i', hi'⟩ := Finite.exists_min (fun j => toLex (v j))
  refine ⟨σ.symm i', fun j => ?_⟩
  rw [Equiv.apply_symm_apply]
  exact Prod.Lex.toLex_le_toLex'.1 (hi' j)

/-- on all sides the winding number is `1`, or on all sides it is `0` -/
theorem wind_side_cases (hs : Simple v σ) :
    (∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = 1) ∨
    (∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = 0) := by
  obtain ⟨l, hl⟩ := wind_side_all hs
  obtain ⟨i, hmin⟩ := hs.exists_lexmin
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hne, h1, h2⟩ := wind_side_value hs i hmin hhalf
  rw [hl (σ i) _ hhalf] at h1 h2
  rcases lt_or_gt_of_ne hne with h | h
  · right; intro k t ht; rw [hl k t ht, h2 h]
  · left; intro k t ht; rw [hl k t ht, h1 h]

/-! ### The region bounded by the curve -/

/-- `cross a b` vanishes on the segment `a b` -/
theorem cross_of_mem_segment {a b x : ℝ × ℝ} (hx : x ∈ segment ℝ a b) : cross a b x = 0 := by
  rw [segment_eq_pt] at hx
  obtain ⟨t, _, rfl⟩ := hx
  simp only [cross, pt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

/-- a segment in the plane is closed -/
theorem isClosed_segment' (a b : ℝ × ℝ) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_pt]
  exact (isCompact_Icc.image (continuous_pt a b)).isClosed

/-- a point off a segment has a neighbourhood which does not meet the segment -/
theorem eventually_notMem_segment {a b x : ℝ × ℝ} (h : x ∉ segment ℝ a b) :
    ∀ᶠ y in 𝓝 x, y ∉ segment ℝ a b :=
  (isClosed_segment' a b).isOpen_compl.mem_nhds h

/-- the closed polygonal curve -/
def curveCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : Set (ℝ × ℝ) := ⋃ i, segment ℝ (v i) (v (σ i))

/-- the closed region bounded by the curve: the curve together with the points around which it
winds -/
def regionCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) : Set (ℝ × ℝ) := curveCyc v σ ∪ {x | wind v σ x ≠ 0}

/-- **(off)** a point off the curve has a neighbourhood inside the region or a neighbourhood
outside the region -/
theorem region_off (v : ι → ℝ × ℝ) (σ : ι ≃ ι) {x : ℝ × ℝ}
    (hx : ∀ i, x ∉ segment ℝ (v i) (v (σ i))) :
    (∀ᶠ y in 𝓝 x, y ∈ regionCyc v σ) ∨ (∀ᶠ y in 𝓝 x, y ∉ regionCyc v σ) := by
  by_cases h : wind v σ x = 0
  · right
    filter_upwards [wind_eventually_eq v σ hx,
      eventually_all.2 (fun i => eventually_notMem_segment (hx i))] with y h1 h2
    rintro (hc | hw)
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hc
      exact h2 i hi
    · exact hw (h1.trans h)
  · left
    filter_upwards [wind_eventually_eq v σ hx] with y h1
    right
    show wind v σ y ≠ 0
    rw [h1]; exact h

/-- a point of a side, not an end point, has a neighbourhood which meets no other side -/
theorem eventually_off_others (hs : Simple v σ) (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t), ∀ j, j ≠ k → y ∉ segment ℝ (v j) (v (σ j)) := by
  apply eventually_all.2
  intro j
  by_cases hj : j = k
  · exact Eventually.of_forall (fun _ h => absurd hj h)
  · exact (eventually_notMem_segment (hs.pt_not_mem k ht.1 ht.2 j hj)).mono (fun y hy _ => hy)

/-- if the winding number on the sides is `1`, the region lies on the left of every side -/
theorem region_left_of_one (hs : Simple v σ)
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = 1)
    (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → y ∈ regionCyc v σ) ∧
      (cross (v k) (v (σ k)) y < 0 → y ∉ regionCyc v σ) := by
  filter_upwards [wind_jump v σ k (hs.ne k) ht.1 ht.2 (hs.pt_not_mem k ht.1 ht.2),
    eventually_off_others hs k ht] with y h12 h3
  obtain ⟨h1, h2⟩ := h12
  rw [hl k t ht] at h1 h2
  constructor
  · intro hc
    right
    show wind v σ y ≠ 0
    rw [h1 hc]; norm_num
  · intro hc
    rintro (hcv | hw)
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hcv
      by_cases hjk : j = k
      · rw [hjk] at hj
        have := cross_of_mem_segment hj
        linarith
      · exact h3 j hjk hj
    · apply hw; rw [h2 hc]; norm_num

/-- if the winding number on the sides is `0`, the region lies on the right of every side -/
theorem region_right_of_zero (hs : Simple v σ)
    (hl : ∀ k t, t ∈ Ioo (0 : ℝ) 1 → wind v σ (pt (v k) (v (σ k)) t) = 0)
    (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → y ∉ regionCyc v σ) ∧
      (cross (v k) (v (σ k)) y < 0 → y ∈ regionCyc v σ) := by
  filter_upwards [wind_jump v σ k (hs.ne k) ht.1 ht.2 (hs.pt_not_mem k ht.1 ht.2),
    eventually_off_others hs k ht] with y h12 h3
  obtain ⟨h1, h2⟩ := h12
  rw [hl k t ht] at h1 h2
  constructor
  · intro hc
    rintro (hcv | hw)
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hcv
      by_cases hjk : j = k
      · rw [hjk] at hj
        have := cross_of_mem_segment hj
        linarith
      · exact h3 j hjk hj
    · exact hw (h1 hc)
  · intro hc
    right
    show wind v σ y ≠ 0
    rw [h2 hc]; norm_num

/-- **(side)** For a simple closed polygon, the region lies locally on the left of every side
(counter-clockwise polygon), or locally on the right of every side (clockwise polygon). -/
theorem region_side (hs : Simple v σ) :
    (∀ k t, t ∈ Ioo (0 : ℝ) 1 → ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → y ∈ regionCyc v σ) ∧
      (cross (v k) (v (σ k)) y < 0 → y ∉ regionCyc v σ)) ∨
    (∀ k t, t ∈ Ioo (0 : ℝ) 1 → ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → y ∉ regionCyc v σ) ∧
      (cross (v k) (v (σ k)) y < 0 → y ∈ regionCyc v σ)) := by
  rcases wind_side_cases hs with hl | hl
  · left; intro k t ht; exact region_left_of_one hs hl k ht
  · right; intro k t ht; exact region_right_of_zero hs hl k ht

/-- the orientation test: if the turn at a lexicographically smallest vertex `v (σ i)` is a left
turn, the region lies on the left of every side -/
theorem region_left_of_turn (hs : Simple v σ) (i : ι)
    (hmin : ∀ j, (v (σ i)).1 ≤ (v j).1 ∧ ((v (σ i)).1 = (v j).1 → (v (σ i)).2 ≤ (v j).2))
    (hturn : 0 < cross (v i) (v (σ i)) (v (σ (σ i))))
    (k : ι) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 (pt (v k) (v (σ k)) t),
      (0 < cross (v k) (v (σ k)) y → y ∈ regionCyc v σ) ∧
      (cross (v k) (v (σ k)) y < 0 → y ∉ regionCyc v σ) := by
  obtain ⟨l, hl⟩ := wind_side_all hs
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := (wind_side_value hs i hmin hhalf).2.1 hturn
  rw [hl (σ i) _ hhalf] at h1
  exact region_left_of_one hs (fun k t ht => (hl k t ht).trans h1) k ht

omit [Fintype ι] in
/-- **(fin)** two different sides have at most two common points (in fact at most one) -/
theorem Simple.inter_finite (hs : Simple v σ) {i j : ι} (hij : i ≠ j) :
    (segment ℝ (v i) (v (σ i)) ∩ segment ℝ (v j) (v (σ j))).Finite := by
  apply (Set.toFinite {v j, v i}).subset
  rintro x ⟨h1, h2⟩
  rcases hs.meet i j hij x h1 h2 with ⟨_, h⟩ | ⟨_, h⟩
  · left; exact h
  · right; exact h

end

end Stein.Polygon
