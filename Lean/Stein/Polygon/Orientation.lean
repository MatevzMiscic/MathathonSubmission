import Stein.Polygon.Jordan
import Stein.Polygon.Convex
import Stein.Geometry.Triangle

/-!
# Orientation and area of simple closed polygons: the shoelace formula

`shoelace v = ∑ k, det (v k) (v (k+1))` (twice the signed area).

* `ae_wind_eq` : for every closed polygonal curve, almost everywhere the winding number is the
  signed number of triangles `(0, v k, v (σ k))` containing the point.
* `volume_region` : for a simple closed polygon, `volume (region v) = |shoelace v| / 2`.
* `shoelace_ne_zero`, `shoelace_pos_iff`, `shoelace_neg_iff` : the sign of the shoelace sum is the
  sign `ε` of the winding number on the inside.
* `region_orientedBoundary_of_shoelace_pos`, `region_orientedBoundary_of_shoelace_neg` : if
  `shoelace v > 0`, the region lies on the left of all sides `v k → v (k+1)`; if `shoelace v < 0`,
  on the left of all reversed sides.  This decides which of the two cases of
  `region_orientedBoundary` (`Stein/Polygon/Region.lean`) holds.

These statements are not used in the proof of the main theorem; they show that `region v` has
the expected area and orientation.
-/

open Set Filter Topology MeasureTheory

namespace Stein.Polygon

noncomputable section

open Complex

/-! ### Triangles as 3-gons -/

/-- the triangle `p, q, r` as a closed polygonal curve with three vertices -/
def tri (p q r : ℝ × ℝ) : Fin 3 → ℝ × ℝ := ![p, q, r]

/-- The angle sum of a triangle. -/
private theorem angSum_tri (p q r x : ℝ × ℝ) :
    angSum (tri p q r) (finRotate 3) x = ang p q x + ang q r x + ang r p x := by
  unfold angSum
  rw [Fin.sum_univ_three]
  rfl

/-- Reversing a side changes the sign of the angle under which it is seen. -/
private theorem ang_swap {a b x : ℝ × ℝ} (hx : x ∉ segment ℝ a b) : ang b a x = -ang a b x := by
  have hs := zq_mem_slitPlane hx
  have e : zq b a x = (zq a b x)⁻¹ := by unfold zq; rw [inv_div]
  unfold ang
  rw [e, arg_inv, ite_eq_right (mem_slitPlane_iff_arg.1 hs).1]

/-- The winding number of a triangle is `0`, `1` or `-1`. -/
private theorem wind_tri_bound (p q r x : ℝ × ℝ) (hp : x ≠ p) (hq : x ≠ q) (hr : x ≠ r) :
    |wind (tri p q r) (finRotate 3) x| ≤ 1 := by
  have h := angSum_eq (tri p q r) (finRotate 3) (x := x) (by
    intro i
    fin_cases i
    · exact hp
    · exact hq
    · exact hr)
  rw [angSum_tri] at h
  have hpi := Real.pi_pos
  have b1 := abs_arg_le_pi (zq p q x)
  have b2 := abs_arg_le_pi (zq q r x)
  have b3 := abs_arg_le_pi (zq r p x)
  have hb : |2 * Real.pi * (wind (tri p q r) (finRotate 3) x : ℝ)| ≤ 3 * Real.pi := by
    rw [← h]
    unfold ang
    have := abs_add_three (arg (zq p q x)) (arg (zq q r x)) (arg (zq r p x))
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hb
  have h2 : |(wind (tri p q r) (finRotate 3) x : ℝ)| < 2 := by
    by_contra hc
    nlinarith [not_lt.1 hc]
  have h3 : |wind (tri p q r) (finRotate 3) x| < 2 := by exact_mod_cast h2
  exact Int.lt_add_one_iff.1 h3

/-- a point strictly on the right of all sides has negative winding number -/
theorem wind_neg_of_right {ι : Type*} [Fintype ι] [Nonempty ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}
    {x : ℝ × ℝ} (h : ∀ i, cross (v i) (v (σ i)) x < 0) : wind v σ x < 0 := by
  have hxv : ∀ i, x ≠ v i := by
    intro i hi
    have := h i
    rw [hi, cross_self_left] at this
    exact lt_irrefl _ this
  have hneg : ∀ i, ang (v i) (v (σ i)) x < 0 :=
    fun i => arg_neg_iff.2 (zq_im_neg (b := v (σ i)) (hxv i) (h i))
  have hsum : angSum v σ x < 0 := Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [angSum_eq v σ hxv] at hsum
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2 : (wind v σ x : ℝ) < 0 := by
    by_contra hc
    have := mul_nonneg hpi.le (not_lt.1 hc)
    linarith
  exact_mod_cast h2

/-- A triangle winds once around a point strictly on the left of its three sides. -/
private theorem wind_tri_ccw {p q r x : ℝ × ℝ} (h1 : 0 < cross p q x) (h2 : 0 < cross q r x)
    (h3 : 0 < cross r p x) : wind (tri p q r) (finRotate 3) x = 1 := by
  have hpos : 0 < wind (tri p q r) (finRotate 3) x := by
    apply wind_pos_of_left
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have hb := wind_tri_bound p q r x
    (fun h => by rw [h, cross_self_left] at h1; exact lt_irrefl _ h1)
    (fun h => by rw [h, cross_self_left] at h2; exact lt_irrefl _ h2)
    (fun h => by rw [h, cross_self_left] at h3; exact lt_irrefl _ h3)
  rw [abs_le] at hb
  omega

/-- A triangle winds `-1` times around a point strictly on the right of its three sides. -/
private theorem wind_tri_cw {p q r x : ℝ × ℝ} (h1 : cross p q x < 0) (h2 : cross q r x < 0)
    (h3 : cross r p x < 0) : wind (tri p q r) (finRotate 3) x = -1 := by
  have hneg : wind (tri p q r) (finRotate 3) x < 0 := by
    apply wind_neg_of_right
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  have hb := wind_tri_bound p q r x
    (fun h => by rw [h, cross_self_left] at h1; exact lt_irrefl _ h1)
    (fun h => by rw [h, cross_self_left] at h2; exact lt_irrefl _ h2)
    (fun h => by rw [h, cross_self_left] at h3; exact lt_irrefl _ h3)
  rw [abs_le] at hb
  omega

/-- A counter-clockwise triangle `a, b, c` lies in the closed side `a b` together with the open
half-plane on its left. -/
private theorem hull3_subset (a b c : ℝ × ℝ) (hc : 0 < cross a b c) :
    convexHull ℝ {a, b, c} ⊆ segment ℝ a b ∪ {y | 0 < cross a b y} := by
  apply convexHull_min _ (convex_side_union a b)
  intro y hy
  rcases hy with rfl | rfl | rfl
  · exact Or.inl (left_mem_segment ℝ _ _)
  · exact Or.inl (right_mem_segment ℝ _ _)
  · exact Or.inr hc

/-- a point of a counter-clockwise triangle which is on no side is strictly on the left of the
three sides -/
private theorem tri_inside {p q r x : ℝ × ℝ} (hc : 0 < cross p q r)
    (hx : x ∈ convexHull ℝ {p, q, r}) (h1 : x ∉ segment ℝ p q) (h2 : x ∉ segment ℝ q r)
    (h3 : x ∉ segment ℝ r p) : 0 < cross p q x ∧ 0 < cross q r x ∧ 0 < cross r p x := by
  have c2 : 0 < cross q r p := by
    have : cross q r p = cross p q r := by unfold cross; ring
    rw [this]; exact hc
  have c3 : 0 < cross r p q := by
    have : cross r p q = cross p q r := by unfold cross; ring
    rw [this]; exact hc
  have e2 : ({q, r, p} : Set (ℝ × ℝ)) = {p, q, r} := by
    ext y; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  have e3 : ({r, p, q} : Set (ℝ × ℝ)) = {p, q, r} := by
    ext y; simp only [mem_insert_iff, mem_singleton_iff]; tauto
  refine ⟨?_, ?_, ?_⟩
  · exact (hull3_subset p q r hc hx).resolve_left h1
  · have := hull3_subset q r p c2 (by rw [e2]; exact hx)
    exact this.resolve_left h2
  · have := hull3_subset r p q c3 (by rw [e3]; exact hx)
    exact this.resolve_left h3

/-- **the winding number of a triangle**, at a point which is on no side: `1` inside a
counter-clockwise triangle, `-1` inside a clockwise triangle, `0` outside -/
theorem wind_tri_value {p q r x : ℝ × ℝ} (h1 : x ∉ segment ℝ p q) (h2 : x ∉ segment ℝ q r)
    (h3 : x ∉ segment ℝ r p) :
    (0 < cross p q r → x ∈ convexHull ℝ {p, q, r} →
      wind (tri p q r) (finRotate 3) x = 1) ∧
    (cross p q r < 0 → x ∈ convexHull ℝ {p, q, r} →
      wind (tri p q r) (finRotate 3) x = -1) ∧
    (x ∉ convexHull ℝ {p, q, r} → wind (tri p q r) (finRotate 3) x = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc hx
    obtain ⟨a1, a2, a3⟩ := tri_inside hc hx h1 h2 h3
    exact wind_tri_ccw a1 a2 a3
  · intro hc hx
    have hc' : 0 < cross p r q := by
      have : cross p r q = -cross p q r := by unfold cross; ring
      rw [this]; linarith
    have e : ({p, r, q} : Set (ℝ × ℝ)) = {p, q, r} := by
      ext y; simp only [mem_insert_iff, mem_singleton_iff]; tauto
    obtain ⟨a1, a2, a3⟩ := tri_inside hc' (by rw [e]; exact hx)
      (by rw [segment_symm]; exact h3) (by rw [segment_symm]; exact h2)
      (by rw [segment_symm]; exact h1)
    have s1 : cross p q x = -cross q p x := cross_swap q p x
    have s2 : cross q r x = -cross r q x := cross_swap r q x
    have s3 : cross r p x = -cross p r x := cross_swap p r x
    exact wind_tri_cw (by rw [s1]; linarith) (by rw [s2]; linarith) (by rw [s3]; linarith)
  · intro hx
    apply wind_eq_zero_of_notMem_convexHull
    intro hmem
    apply hx
    refine convexHull_mono ?_ hmem
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- **the winding number of a closed polygonal curve is the sum of the winding numbers of the
triangles `(O, v k, v (σ k))`**, at every point which is not on the segments `O (v k)` -/
theorem wind_eq_sum_tri (v : ι → ℝ × ℝ) (σ : ι ≃ ι) {O x : ℝ × ℝ} (hxO : x ≠ O)
    (hxv : ∀ i, x ≠ v i) (hO : ∀ i, x ∉ segment ℝ O (v i)) :
    wind v σ x = ∑ k, wind (tri O (v k) (v (σ k))) (finRotate 3) x := by
  have hsum : ∑ k, angSum (tri O (v k) (v (σ k))) (finRotate 3) x = angSum v σ x := by
    simp only [angSum_tri]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 : ∑ k, ang (v (σ k)) O x = ∑ k, ang (v k) O x :=
      Equiv.sum_comp σ (fun j => ang (v j) O x)
    have e2 : ∑ k, ang (v k) O x = -∑ k, ang O (v k) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => ang_swap (hO k))
    unfold angSum
    rw [e1, e2]
    ring
  have htri : ∀ k, angSum (tri O (v k) (v (σ k))) (finRotate 3) x =
      2 * Real.pi * wind (tri O (v k) (v (σ k))) (finRotate 3) x := by
    intro k
    apply angSum_eq
    intro i
    fin_cases i
    · exact hxO
    · exact hxv k
    · exact hxv (σ k)
  have h2 := angSum_eq v σ hxv
  rw [← hsum] at h2
  simp only [htri] at h2
  rw [← Finset.mul_sum] at h2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have := mul_left_cancel₀ hpi h2
  exact_mod_cast this.symm

end cyc

/-! ### Measure -/

/-- Segments are null sets. -/
private theorem volume_segment (a b : ℝ × ℝ) : volume (segment ℝ a b) = 0 := by
  have h := Stein.volume_triangle a a b
  rw [insert_eq_of_mem (mem_insert a {b}), convexHull_pair] at h
  rw [h]
  simp [Stein.det]

/-- the sign of a real number, as a real number -/
def sg (r : ℝ) : ℝ := if 0 < r then 1 else if r < 0 then -1 else 0

/-- `sg r * |r| = r`, halved. -/
private theorem sg_mul_abs (r : ℝ) : sg r * (|r| / 2) = r / 2 := by
  unfold sg
  split_ifs with h1 h2
  · rw [abs_of_pos h1]; ring
  · rw [abs_of_neg h2]; ring
  · have : r = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    rw [this]; simp

/-- `cross 0 a b` is the determinant of `a` and `b`. -/
private theorem cross_zero (a b : ℝ × ℝ) : cross 0 a b = det a b := by
  simp [cross, det]

section cyc

variable {ι : Type*} [Fintype ι] {v : ι → ℝ × ℝ} {σ : ι ≃ ι}

/-- **Almost everywhere, the winding number of a closed polygonal curve is the signed number of
the triangles `(0, v k, v (σ k))` containing the point.** -/
theorem ae_wind_eq (v : ι → ℝ × ℝ) (σ : ι ≃ ι) :
    ∀ᵐ x : ℝ × ℝ, x ∉ curveCyc v σ ∧ (wind v σ x : ℝ) =
      ∑ k, sg (det (v k) (v (σ k))) *
        (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}).indicator (1 : ℝ × ℝ → ℝ) x := by
  have h1 : ∀ᵐ x : ℝ × ℝ, ∀ k, x ∉ segment ℝ (v k) (v (σ k)) :=
    ae_all_iff.2 (fun k => measure_eq_zero_iff_ae_notMem.1 (volume_segment _ _))
  have h2 : ∀ᵐ x : ℝ × ℝ, ∀ k, x ∉ segment ℝ 0 (v k) :=
    ae_all_iff.2 (fun k => measure_eq_zero_iff_ae_notMem.1 (volume_segment _ _))
  have h3 : ∀ᵐ x : ℝ × ℝ, ∀ k, det (v k) (v (σ k)) = 0 →
      x ∉ convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)} := by
    apply ae_all_iff.2
    intro k
    by_cases hd : det (v k) (v (σ k)) = 0
    · have : volume (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}) = 0 := by
        rw [Stein.volume_triangle, sub_zero, sub_zero, hd]; simp
      exact (measure_eq_zero_iff_ae_notMem.1 this).mono (fun x hx _ => hx)
    · exact Eventually.of_forall (fun x h => absurd h hd)
  filter_upwards [h1, h2, h3] with x a1 a2 a3
  refine ⟨notMem_curveCyc.2 a1, ?_⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [wind, angSum]
  have hxO : x ≠ 0 := fun h => a2 i₀ (h ▸ left_mem_segment ℝ _ _)
  have hxv : ∀ i, x ≠ v i := fun i h => a1 i (h ▸ left_mem_segment ℝ _ _)
  rw [wind_eq_sum_tri v σ hxO hxv a2]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  obtain ⟨t1, t2, t3⟩ := wind_tri_value (p := 0) (a2 k) (a1 k)
    (by rw [segment_symm]; exact a2 (σ k))
  rw [cross_zero] at t1 t2
  by_cases hx : x ∈ convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}
  · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
    have hd : det (v k) (v (σ k)) ≠ 0 := fun h => a3 k h hx
    rcases lt_or_gt_of_ne hd with h | h
    · rw [t2 h hx, sg, ite_eq_right (not_lt.2 h.le), ite_eq_left h]; norm_num
    · rw [t1 h hx, sg, ite_eq_left h]; norm_num
  · rw [indicator_of_notMem hx, mul_zero, t3 hx]; norm_num

/-- the area of the region in terms of the sign `ε` of the winding number -/
theorem volume_regionCyc (v : ι → ℝ × ℝ) (σ : ι ≃ ι) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hval : ∀ x, x ∉ curveCyc v σ → wind v σ x = 0 ∨ wind v σ x = ε) :
    (volume (regionCyc v σ)).toReal = ε * ((∑ k, det (v k) (v (σ k))) / 2) := by
  have hmeas : MeasurableSet (regionCyc v σ) := (isClosed_regionCyc v σ).measurableSet
  have hΔm : ∀ k, MeasurableSet (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}) := fun k =>
    (Set.Finite.isClosed_convexHull ℝ (by simp)).measurableSet
  have hΔfin : ∀ k, volume (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}) ≠ ⊤ := by
    intro k
    rw [Stein.volume_triangle]
    exact ENNReal.ofReal_ne_top
  have hae : (regionCyc v σ).indicator (1 : ℝ × ℝ → ℝ) =ᵐ[volume] fun x =>
      (ε : ℝ) * ∑ k, sg (det (v k) (v (σ k))) *
        (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}).indicator (1 : ℝ × ℝ → ℝ) x := by
    filter_upwards [ae_wind_eq v σ] with x ⟨hxc, hx⟩
    rw [← hx]
    by_cases hw : wind v σ x = 0
    · have hnot : x ∉ regionCyc v σ := by
        rintro (h | h)
        · exact hxc h
        · exact h hw
      rw [indicator_of_notMem hnot, hw]; simp
    · have hin : x ∈ regionCyc v σ := Or.inr hw
      rw [indicator_of_mem hin, (hval x hxc).resolve_left hw]
      rcases hε with rfl | rfl <;> norm_num
  have hint : ∀ k, Integrable (fun x => sg (det (v k) (v (σ k))) *
      (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}).indicator (1 : ℝ × ℝ → ℝ) x) := fun k =>
    ((integrableOn_const (hΔfin k)).integrable_indicator (hΔm k)).const_mul _
  calc (volume (regionCyc v σ)).toReal
      = ∫ x, (regionCyc v σ).indicator (1 : ℝ × ℝ → ℝ) x := (integral_indicator_one hmeas).symm
    _ = ∫ x, (ε : ℝ) * ∑ k, sg (det (v k) (v (σ k))) *
        (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)}).indicator (1 : ℝ × ℝ → ℝ) x :=
          integral_congr_ae hae
    _ = ε * ∑ k, sg (det (v k) (v (σ k))) *
        (volume (convexHull ℝ {(0 : ℝ × ℝ), v k, v (σ k)})).toReal := by
          rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [integral_const_mul, integral_indicator_one (hΔm k)]
          rfl
    _ = ε * ((∑ k, det (v k) (v (σ k))) / 2) := by
          congr 1
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k _
          rw [Stein.volume_triangle, ENNReal.toReal_ofReal (by positivity), sub_zero, sub_zero,
            sg_mul_abs]

end cyc

variable {m : ℕ}

/-! ### Simple closed polygons: area and orientation -/

/-- the shoelace sum `∑ k, det (v k) (v (k+1))`: twice the signed area of the polygon -/
def shoelace (v : Fin (m + 3) → ℝ × ℝ) : ℝ := ∑ k, det (v k) (v (k + 1))

/-- the area of the region in terms of the sign `ε` of the winding number (any closed polygonal
curve whose winding number takes only the values `0` and `ε` off the curve) -/
theorem volume_region_signed (v : Fin (m + 3) → ℝ × ℝ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hval : ∀ x, x ∉ boundary v → windingNumber v x = 0 ∨ windingNumber v x = ε) :
    (volume (region v)).toReal = ε * (shoelace v / 2) := by
  have h := volume_regionCyc v (finRotate (m + 3)) hε
    (by simpa only [boundary_eq, windingNumber_eq] using hval)
  rw [region_eq, h]
  simp only [shoelace, rot_apply]

/-- The region of a simple closed polygon has positive area. -/
theorem volume_region_pos (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    0 < (volume (region v)).toReal := by
  have h1 : 0 < volume (region v \ boundary v) :=
    (isOpen_inner v hv).measure_pos volume (isConnected_inner v hv).nonempty
  have h2 : volume (region v \ boundary v) ≤ volume (region v) := measure_mono sdiff_subset
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le h1 h2))
    ((isCompact_region v).measure_lt_top (μ := volume)).ne

/-- **Shoelace formula.**  The area (Lebesgue measure) of the region bounded by a simple
closed polygon is `|∑ k, det (v k) (v (k+1))| / 2`. -/
theorem volume_region (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    volume (region v) = ENNReal.ofReal (|shoelace v| / 2) := by
  obtain ⟨ε, h1, h2, -, -⟩ := windingNumber_values v hv
  have hs := volume_region_signed v h1 h2
  have hp := volume_region_pos v hv
  have hfin := ((isCompact_region v).measure_lt_top (μ := volume)).ne
  rw [← ENNReal.ofReal_toReal hfin, hs]
  congr 1
  rw [hs] at hp
  rcases h1 with rfl | rfl
  · push_cast at hp ⊢
    rw [abs_of_pos (by linarith)]; ring
  · push_cast at hp ⊢
    rw [abs_of_neg (by linarith)]; ring

/-- the shoelace sum of a simple closed polygon is not zero -/
theorem shoelace_ne_zero (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) : shoelace v ≠ 0 := by
  obtain ⟨ε, h1, h2, -, -⟩ := windingNumber_values v hv
  have hp := volume_region_pos v hv
  rw [volume_region_signed v h1 h2] at hp
  intro h0
  rw [h0] at hp
  simp at hp

/-- **Orientation.**  The shoelace sum of a simple closed polygon is positive iff the winding
number is `1` on the inside (counter-clockwise polygon). -/
theorem shoelace_pos_iff (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    0 < shoelace v ↔ ∀ x, x ∉ boundary v → windingNumber v x = 0 ∨ windingNumber v x = 1 := by
  constructor
  · intro h
    obtain ⟨ε, h1, h2, -, -⟩ := windingNumber_values v hv
    have hp := volume_region_pos v hv
    rw [volume_region_signed v h1 h2] at hp
    rcases h1 with rfl | rfl
    · exact h2
    · exfalso
      push_cast at hp
      linarith
  · intro h
    have hp := volume_region_pos v hv
    rw [volume_region_signed v (Or.inl rfl) h] at hp
    push_cast at hp
    linarith

/-- the shoelace sum of a simple closed polygon is negative iff the winding number is `-1` on the
inside (clockwise polygon) -/
theorem shoelace_neg_iff (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v) :
    shoelace v < 0 ↔ ∀ x, x ∉ boundary v → windingNumber v x = 0 ∨ windingNumber v x = -1 := by
  constructor
  · intro h
    obtain ⟨ε, h1, h2, -, -⟩ := windingNumber_values v hv
    have hp := volume_region_pos v hv
    rw [volume_region_signed v h1 h2] at hp
    rcases h1 with rfl | rfl
    · exfalso
      push_cast at hp
      linarith
    · exact h2
  · intro h
    have hp := volume_region_pos v hv
    rw [volume_region_signed v (Or.inr rfl) h] at hp
    push_cast at hp
    linarith

/-- inside a simple closed polygon with positive shoelace sum the winding number is `1` -/
theorem windingNumber_eq_one_of_shoelace_pos (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    (h : 0 < shoelace v) {x : ℝ × ℝ} (hx : x ∉ boundary v) (hr : x ∈ region v) :
    windingNumber v x = 1 := by
  rcases (shoelace_pos_iff v hv).1 h x hx with h0 | h1
  · rcases hr with hb | hw
    · exact absurd hb hx
    · exact absurd h0 hw
  · exact h1

/-- inside a simple closed polygon with negative shoelace sum the winding number is `-1` -/
theorem windingNumber_eq_neg_one_of_shoelace_neg (v : Fin (m + 3) → ℝ × ℝ)
    (hv : SimplePolygon v) (h : shoelace v < 0) {x : ℝ × ℝ} (hx : x ∉ boundary v)
    (hr : x ∈ region v) : windingNumber v x = -1 := by
  rcases (shoelace_neg_iff v hv).1 h x hx with h0 | h1
  · rcases hr with hb | hw
    · exact absurd hb hx
    · exact absurd h0 hw
  · exact h1

/-- **Orientation test by the shoelace sum.**  If `shoelace v > 0`, the region of the simple
closed polygon `v` lies on the left of all sides `v k → v (k+1)`. -/
theorem region_orientedBoundary_of_shoelace_pos (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    (h : 0 < shoelace v) : OrientedBoundary (region v) v (fun k => v (k + 1)) := by
  have hs := hv.simple
  rcases wind_side_cases hs with hl | hl
  · rw [region_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply region_off
      simpa only [rot_apply] using hx
    · intro k x hx hxa hxb _
      obtain ⟨t, ht, rfl⟩ := mem_segment_pt hx hxa hxb
      have := region_left_of_one hs hl k ht
      simpa only [rot_apply] using this
    · intro j k hjk
      have := hs.inter_finite hjk
      simpa only [rot_apply] using this
  · exfalso
    obtain ⟨-, ⟨x, hxc, hxw⟩⟩ := exists_wind_eq hs hl
    rw [← boundary_eq] at hxc
    rw [← windingNumber_eq] at hxw
    rcases (shoelace_pos_iff v hv).1 h x hxc with h0 | h1
    · rw [h0] at hxw; norm_num at hxw
    · rw [h1] at hxw; norm_num at hxw

/-- If `shoelace v < 0`, the region of the simple closed polygon `v` lies on the left of all
reversed sides `v (k+1) → v k`. -/
theorem region_orientedBoundary_of_shoelace_neg (v : Fin (m + 3) → ℝ × ℝ) (hv : SimplePolygon v)
    (h : shoelace v < 0) : OrientedBoundary (region v) (fun k => v (k + 1)) v := by
  have hs := hv.simple
  rcases wind_side_cases hs with hl | hl
  · exfalso
    obtain ⟨⟨x, hxc, hxw⟩, -⟩ := exists_wind_eq hs hl
    rw [← boundary_eq] at hxc
    rw [← windingNumber_eq] at hxw
    rcases (shoelace_neg_iff v hv).1 h x hxc with h0 | h1
    · rw [h0] at hxw; norm_num at hxw
    · rw [h1] at hxw; norm_num at hxw
  · rw [region_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply region_off
      intro i
      rw [rot_apply, segment_symm]
      exact hx i
    · intro k x hx hxa hxb _
      rw [segment_symm] at hx
      obtain ⟨t, ht, rfl⟩ := mem_segment_pt hx hxb hxa
      have := region_right_of_zero hs hl k ht
      simp only [rot_apply] at this
      filter_upwards [this] with y hy
      rw [cross_swap]
      exact ⟨fun hc => hy.2 (by linarith), fun hc => hy.1 (by linarith)⟩
    · intro j k hjk
      have := hs.inter_finite hjk
      simp only [rot_apply] at this
      rw [segment_symm ℝ (v (j + 1)), segment_symm ℝ (v (k + 1))]
      exact this

/-- the shoelace sum of the unit square is `2` (area `1`) -/
theorem shoelace_unitSquare : shoelace unitSquare = 2 := by
  simp [shoelace, Fin.sum_univ_four, unitSquare, det]
  norm_num

end

end Stein.Polygon
