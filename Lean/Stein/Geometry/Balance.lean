import Stein.Geometry.Triangle

/-!
# Lemma 4.1 (Balance)

`Stein.balance`: let `S ⊆ ℝ²` lie on the left of its oriented boundary `A k → B k`
(`Stein.OrientedBoundary`), and let `S` be the union of finitely many counter-clockwise
triangles with pairwise disjoint interiors.  Then for every direction `d ≠ 0` the side vectors of
the triangles parallel to `d` sum to the sum of the boundary vectors `B k - A k` parallel to `d`.

Method ("left minus right").  Fix `d` and a line `L` parallel to `d`, and let `n` be the left
normal of `d`.  For a set `X` and a point `x ∈ L` consider the jump
`j_X(x) = 1_X(x + δ n) - 1_X(x - δ n)` for small `δ > 0`.  For all but finitely many `x ∈ L`:
for a counter-clockwise triangle, `j` is `+1` / `-1` on the open side lying on `L` and running
in the direction `d` / `-d`, and `0` elsewhere (`tri_generic`); the same holds for `S` and its
boundary sides (`bdry_generic`); and `1_S = Σ 1_{T_i}` at the points `x ± δ n` (`sum_ind`).
Integrating the resulting identity of step functions along `L` gives the claim for the sides
on `L` (`balance_level`); summing over the finitely many lines `L` gives the lemma.
-/

open Set Filter Topology MeasureTheory

namespace Stein

noncomputable section

/-! ### Coordinates adapted to the direction `d` and signed indicators of sides -/

/-- The indicator of a proposition, as a real number: `1` if `P` holds and `0` otherwise. -/
private def ind (P : Prop) : ℝ := by classical exact if P then 1 else 0

private theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

private theorem ind_neg {P : Prop} (h : ¬P) : ind P = 0 := by simp [ind, h]

private theorem ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [propext h]

/-- The dot product of `x` with `d`; the coordinate of `x` along the direction `d`. -/
private def dt (d x : ℝ × ℝ) : ℝ := x.1 * d.1 + x.2 * d.2

/-- The point `x` with `det d x = c` and `dt d x = τ`: the point with parameter `τ` of the line
`det d · = c` parallel to `d`. -/
private def pt (d : ℝ × ℝ) (c τ : ℝ) : ℝ × ℝ :=
  ((τ * d.1 - c * d.2) / (d.1 ^ 2 + d.2 ^ 2), (τ * d.2 + c * d.1) / (d.1 ^ 2 + d.2 ^ 2))

/-- `cross` in the coordinates `(det d ·, dt d ·)`. -/
private theorem cross_coord (d a b y : ℝ × ℝ) :
    (d.1 ^ 2 + d.2 ^ 2) * cross a b y
      = (dt d b - dt d a) * (det d y - det d a) - (dt d y - dt d a) * (det d b - det d a) := by
  simp only [cross, det, dt]
  ring

private theorem det_comb (d a b : ℝ × ℝ) (s t : ℝ) :
    det d (s • a + t • b) = s * det d a + t * det d b := by
  simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem dt_comb (d a b : ℝ × ℝ) (s t : ℝ) :
    dt d (s • a + t • b) = s * dt d a + t * dt d b := by
  simp only [dt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private theorem det_nrm (d a b : ℝ × ℝ) : det (b - a) (nrm d) = dt d b - dt d a := by
  simp only [det, nrm, dt, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem det_neg_nrm (d a b : ℝ × ℝ) : det (b - a) (-nrm d) = -(dt d b - dt d a) := by
  simp only [det, nrm, dt, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
  ring

/-- The signed indicator of the open segment `a → b` in the parameter `τ = dt d ·` of the line
`det d · = c`, if the segment lies on that line (`+1` if it runs in the direction `d`, `-1` if it
runs in the direction `-d`), and `0` if it does not lie on that line. -/
private def g (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) (τ : ℝ) : ℝ :=
  if det d a = c ∧ det d b = c then
    ind (dt d a < τ ∧ τ < dt d b) - ind (dt d b < τ ∧ τ < dt d a)
  else 0

/-- The signed length (times `|d|`) of the segment `a → b` if it lies on the line
`det d · = c`, and `0` otherwise. -/
private def mlev (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) : ℝ :=
  if det d a = c ∧ det d b = c then dt d b - dt d a else 0

/-- The finitely many exceptional parameters `τ` of the line `det d · = c` for the side `a → b`:
the parameters of `a` and `b`, and of the point where the line of the side crosses the line. -/
private def Bad (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) : Set ℝ :=
  {τ | τ = dt d a ∨ τ = dt d b ∨ (det d b ≠ det d a ∧
    τ = dt d a + (dt d b - dt d a) * (c - det d a) / (det d b - det d a))}

private theorem Bad_finite (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) : (Bad d c a b).Finite := by
  apply (Set.toFinite {dt d a, dt d b,
    dt d a + (dt d b - dt d a) * (c - det d a) / (det d b - det d a)}).subset
  intro τ h
  rcases h with h | h | ⟨_, h⟩ <;> simp [h]

private theorem g_of_not_on {d : ℝ × ℝ} {c : ℝ} {a b : ℝ × ℝ} (h : ¬(det d a = c ∧ det d b = c))
    (τ : ℝ) : g d c a b τ = 0 := by
  simp [g, h]

/-- The sign of `cross a b` is eventually constant along a ray starting at a point off the line
`a b`. -/
private theorem ev_sign (a b x n : ℝ × ℝ) (h : cross a b x ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, (0 ≤ cross a b (x + δ • n) ↔ 0 < cross a b x) ∧
      cross a b (x + δ • n) ≠ 0 := by
  have ht : Tendsto (fun δ : ℝ => cross a b (x + δ • n)) (𝓝[>] 0) (𝓝 (cross a b x)) :=
    ((cross_continuous a b).tendsto x).comp (tendsto_add_smul x n)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [ht.eventually (gt_mem_nhds hlt)] with δ hδ
    exact ⟨⟨fun h' => absurd h' (not_le.2 hδ), fun h' => absurd h' (not_lt.2 hlt.le)⟩, hδ.ne⟩
  · filter_upwards [ht.eventually (lt_mem_nhds hgt)] with δ hδ
    exact ⟨⟨fun _ => hgt, fun _ => hδ.le⟩, hδ.ne'⟩

private theorem sign_helper {N e h t : ℝ} (hNpos : 0 < N) (he : 0 < e) (heq : N * h = e * t) :
    0 < h ↔ 0 < t := by
  rw [← mul_pos_iff_of_pos_left hNpos, heq, mul_pos_iff_of_pos_left he]

/-! ### The jump of an indicator function across a line parallel to `d` -/

section line

variable {d : ℝ × ℝ} (hN : 0 < d.1 ^ 2 + d.2 ^ 2)

include hN

private theorem det_pt (c τ : ℝ) : det d (pt d c τ) = c := by
  have := hN.ne'
  simp only [det, pt]
  field_simp
  ring

private theorem dt_pt (c τ : ℝ) : dt d (pt d c τ) = τ := by
  have := hN.ne'
  simp only [dt, pt]
  field_simp
  ring

/-- A point is determined by its coordinates `(det d ·, dt d ·)`. -/
private theorem eq_of_coords {x y : ℝ × ℝ} (h1 : det d x = det d y) (h2 : dt d x = dt d y) :
    x = y := by
  simp only [det, dt] at h1 h2
  have e1 : (d.1 ^ 2 + d.2 ^ 2) * (x.1 - y.1) = 0 := by linear_combination d.1 * h2 - d.2 * h1
  have e2 : (d.1 ^ 2 + d.2 ^ 2) * (x.2 - y.2) = 0 := by linear_combination d.2 * h2 + d.1 * h1
  have f1 := (mul_eq_zero.1 e1).resolve_left hN.ne'
  have f2 := (mul_eq_zero.1 e2).resolve_left hN.ne'
  exact Prod.ext (by linarith) (by linarith)

private theorem cross_pt (a b : ℝ × ℝ) (c τ : ℝ) :
    (d.1 ^ 2 + d.2 ^ 2) * cross a b (pt d c τ)
      = (dt d b - dt d a) * (c - det d a) - (τ - dt d a) * (det d b - det d a) := by
  rw [cross_coord d, det_pt hN, dt_pt hN]

/-- If the side `a → b` lies on the line, `cross a b` vanishes on the line. -/
private theorem cross_pt_on {a b : ℝ × ℝ} {c : ℝ} (ha : det d a = c) (hb : det d b = c)
    (τ : ℝ) : cross a b (pt d c τ) = 0 := by
  have h := cross_pt hN a b c τ
  rw [ha, hb, sub_self, mul_zero, mul_zero, sub_zero] at h
  exact (mul_eq_zero.1 h).resolve_left hN.ne'

/-- On a side lying on the line, `cross` along the normal is `δ * (dt d b - dt d a)`. -/
private theorem cross_on {a b : ℝ × ℝ} {c : ℝ} (ha : det d a = c) (hb : det d b = c) (τ δ : ℝ) :
    cross a b (pt d c τ + δ • nrm d) = δ * (dt d b - dt d a) ∧
      cross a b (pt d c τ + δ • (-nrm d)) = -(δ * (dt d b - dt d a)) := by
  rw [cross_add_smul, cross_add_smul, cross_pt_on hN ha hb, det_nrm, det_neg_nrm]
  constructor <;> ring

/-- A generic point of the line is off the line of a side, unless the side lies on the line. -/
private theorem generic {a b : ℝ × ℝ} {c τ : ℝ} (hab : a ≠ b) (hτ : τ ∉ Bad d c a b) :
    cross a b (pt d c τ) ≠ 0 ∨ (det d a = c ∧ det d b = c) := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨h0, hon⟩ := hcon
  have h := cross_pt hN a b c τ
  rw [h0, mul_zero] at h
  by_cases hc : det d b = det d a
  · rw [hc, sub_self, mul_zero, sub_zero] at h
    have ht : dt d b - dt d a ≠ 0 := by
      intro ht
      exact hab (eq_of_coords hN hc.symm (by linarith))
    have hca : c - det d a = 0 := (mul_eq_zero.1 h.symm).resolve_left ht
    exact hon ⟨by linarith, by linarith⟩
  · apply hτ
    right; right
    refine ⟨hc, ?_⟩
    have hc' : det d b - det d a ≠ 0 := sub_ne_zero.2 hc
    field_simp
    linarith

/-- The jump of the indicator of a counter-clockwise triangle across its side `p → q`, at a
generic point of the line of that side. -/
private theorem tri_on {p q r : ℝ × ℝ} {c τ : ℝ} (hD : 0 < det (q - p) (r - p))
    (hp : det d p = c) (hq : det d q = c)
    (h2 : cross q r (pt d c τ) ≠ 0) (h3 : cross r p (pt d c τ) ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ind (pt d c τ + δ • nrm d ∈ Tc p q r)
      - ind (pt d c τ + δ • (-nrm d) ∈ Tc p q r) = g d c p q τ := by
  have hND : (d.1 ^ 2 + d.2 ^ 2) * det (q - p) (r - p)
      = (dt d q - dt d p) * (det d r - c) := by
    have h := cross_coord d p q r
    rw [cross_eq_det, hp, hq, sub_self, mul_zero, sub_zero] at h
    exact h
  have hNh3 : (d.1 ^ 2 + d.2 ^ 2) * cross r p (pt d c τ)
      = (det d r - c) * (τ - dt d p) := by
    rw [cross_pt hN, hp]; ring
  have hNh2 : (d.1 ^ 2 + d.2 ^ 2) * cross q r (pt d c τ)
      = (det d r - c) * (dt d q - τ) := by
    rw [cross_pt hN, hq]; ring
  have hNh3' : (d.1 ^ 2 + d.2 ^ 2) * cross r p (pt d c τ)
      = (-(det d r - c)) * (dt d p - τ) := by rw [hNh3]; ring
  have hNh2' : (d.1 ^ 2 + d.2 ^ 2) * cross q r (pt d c τ)
      = (-(det d r - c)) * (τ - dt d q) := by rw [hNh2]; ring
  have hprod : 0 < (dt d q - dt d p) * (det d r - c) := by
    rw [← hND]; exact mul_pos hN hD
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := eventually_mem_nhdsWithin
  filter_upwards [ev_sign q r (pt d c τ) (nrm d) h2, ev_sign q r (pt d c τ) (-nrm d) h2,
    ev_sign r p (pt d c τ) (nrm d) h3, ev_sign r p (pt d c τ) (-nrm d) h3, hpos]
    with δ e2 e2' e3 e3' hδ
  obtain ⟨c1, c1'⟩ := cross_on hN hp hq τ δ
  have m1 : pt d c τ + δ • nrm d ∈ Tc p q r ↔ (dt d p < τ ∧ τ < dt d q) := by
    simp only [Tc, mem_ofPred_eq, c1, e2.1, e3.1]
    constructor
    · rintro ⟨hk, hh2, hh3⟩
      have hk' : 0 < dt d q - dt d p := by
        rcases hk.lt_or_eq with h | h
        · exact (mul_pos_iff_of_pos_left hδ).1 h
        · exfalso
          rcases mul_eq_zero.1 h.symm with h | h
          · exact hδ.ne' h
          · rw [h, zero_mul] at hprod; exact lt_irrefl _ hprod
      have he : 0 < det d r - c := (mul_pos_iff_of_pos_left hk').1 hprod
      exact ⟨by linarith [(sign_helper hN he hNh3).1 hh3],
        by linarith [(sign_helper hN he hNh2).1 hh2]⟩
    · rintro ⟨ha, hb⟩
      have hk' : 0 < dt d q - dt d p := by linarith
      have he : 0 < det d r - c := (mul_pos_iff_of_pos_left hk').1 hprod
      exact ⟨(mul_pos hδ hk').le, (sign_helper hN he hNh2).2 (by linarith),
        (sign_helper hN he hNh3).2 (by linarith)⟩
  have m2 : pt d c τ + δ • (-nrm d) ∈ Tc p q r ↔ (dt d q < τ ∧ τ < dt d p) := by
    simp only [Tc, mem_ofPred_eq, c1', e2'.1, e3'.1]
    constructor
    · rintro ⟨hk, hh2, hh3⟩
      have hk' : 0 < -(dt d q - dt d p) := by
        have hk2 : 0 ≤ δ * (-(dt d q - dt d p)) := by linarith
        rcases hk2.lt_or_eq with h | h
        · exact (mul_pos_iff_of_pos_left hδ).1 h
        · exfalso
          rcases mul_eq_zero.1 h.symm with h | h
          · exact hδ.ne' h
          · have : dt d q - dt d p = 0 := by linarith
            rw [this, zero_mul] at hprod; exact lt_irrefl _ hprod
      have he : 0 < -(det d r - c) := by
        have : 0 < (-(dt d q - dt d p)) * (-(det d r - c)) := by linarith
        exact (mul_pos_iff_of_pos_left hk').1 this
      exact ⟨by linarith [(sign_helper hN he hNh2').1 hh2],
        by linarith [(sign_helper hN he hNh3').1 hh3]⟩
    · rintro ⟨ha, hb⟩
      have hk' : 0 < -(dt d q - dt d p) := by linarith
      have he : 0 < -(det d r - c) := by
        have : 0 < (-(dt d q - dt d p)) * (-(det d r - c)) := by linarith
        exact (mul_pos_iff_of_pos_left hk').1 this
      refine ⟨?_, (sign_helper hN he hNh2').2 (by linarith),
        (sign_helper hN he hNh3').2 (by linarith)⟩
      have := mul_pos hδ hk'
      linarith
  rw [ind_congr m1, ind_congr m2]
  simp only [g, hp, hq, and_self, ↓reduceIte]

omit hN in
private theorem Tc_rot (p q r : ℝ × ℝ) : Tc q r p = Tc p q r := by
  ext x
  simp only [Tc, mem_ofPred_eq]
  tauto

omit hN in
private theorem ne_of_det_pos {p q r : ℝ × ℝ} (hD : 0 < det (q - p) (r - p)) :
    p ≠ q ∧ q ≠ r ∧ r ≠ p := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    simp [det] at hD
  · rintro rfl
    have : det (q - p) (q - p) = 0 := by simp only [det]; ring
    rw [this] at hD
    exact lt_irrefl _ hD
  · rintro rfl
    simp [det] at hD

omit hN in
private theorem not_three_on {p q r : ℝ × ℝ} {c : ℝ} (hD : 0 < det (q - p) (r - p))
    (hp : det d p = c) (hq : det d q = c) (hr : det d r = c) : d.1 ^ 2 + d.2 ^ 2 ≤ 0 := by
  by_contra hNpos
  rw [not_le] at hNpos
  have h := cross_coord d p q r
  rw [cross_eq_det, hp, hq, hr, sub_self, mul_zero, mul_zero, sub_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact hNpos.ne' h
  · exact hD.ne' h

/-- **The jump of the indicator of a counter-clockwise triangle** at a generic point of the line
is the sum of the signed indicators of its sides on the line. -/
private theorem tri_generic {p q r : ℝ × ℝ} {c τ : ℝ} (hD : 0 < det (q - p) (r - p))
    (h1 : τ ∉ Bad d c p q) (h2 : τ ∉ Bad d c q r) (h3 : τ ∉ Bad d c r p) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ind (pt d c τ + δ • nrm d ∈ Tc p q r)
      - ind (pt d c τ + δ • (-nrm d) ∈ Tc p q r)
        = g d c p q τ + g d c q r τ + g d c r p τ := by
  obtain ⟨hpq, hqr, hrp⟩ := ne_of_det_pos hD
  have hD2 : 0 < det (r - q) (p - q) := by
    linarith [cross_sum q r p q, cross_sum p q r q]
  have hD3 : 0 < det (p - r) (q - r) := by
    linarith [cross_sum r p q r, cross_sum p q r r]
  have hnot : ∀ {a b : ℝ × ℝ}, cross a b (pt d c τ) ≠ 0 → ¬(det d a = c ∧ det d b = c) :=
    fun hne hon => hne (cross_pt_on hN hon.1 hon.2 τ)
  rcases generic hN hpq h1 with g1 | on1
  · rcases generic hN hqr h2 with g2 | on2
    · rcases generic hN hrp h3 with g3 | on3
      · filter_upwards [ev_sign p q (pt d c τ) (nrm d) g1, ev_sign p q (pt d c τ) (-nrm d) g1,
          ev_sign q r (pt d c τ) (nrm d) g2, ev_sign q r (pt d c τ) (-nrm d) g2,
          ev_sign r p (pt d c τ) (nrm d) g3, ev_sign r p (pt d c τ) (-nrm d) g3]
          with δ e1 e1' e2 e2' e3 e3'
        have m1 : pt d c τ + δ • nrm d ∈ Tc p q r ↔ (0 < cross p q (pt d c τ) ∧
            0 < cross q r (pt d c τ) ∧ 0 < cross r p (pt d c τ)) := by
          simp only [Tc, mem_ofPred_eq, e1.1, e2.1, e3.1]
        have m2 : pt d c τ + δ • (-nrm d) ∈ Tc p q r ↔ (0 < cross p q (pt d c τ) ∧
            0 < cross q r (pt d c τ) ∧ 0 < cross r p (pt d c τ)) := by
          simp only [Tc, mem_ofPred_eq, e1'.1, e2'.1, e3'.1]
        rw [ind_congr m1, ind_congr m2, g_of_not_on (hnot g1), g_of_not_on (hnot g2),
          g_of_not_on (hnot g3)]
        ring
      · have h := tri_on hN hD3 on3.1 on3.2 g1 g2
        rw [Tc_rot q r p, Tc_rot p q r] at h
        filter_upwards [h] with δ hδ
        rw [hδ, g_of_not_on (hnot g1), g_of_not_on (hnot g2)]
        ring
    · rcases generic hN hrp h3 with g3 | on3
      · have h := tri_on hN hD2 on2.1 on2.2 g3 g1
        rw [Tc_rot p q r] at h
        filter_upwards [h] with δ hδ
        rw [hδ, g_of_not_on (hnot g1), g_of_not_on (hnot g3)]
        ring
      · exact absurd (not_three_on hD on3.2 on2.1 on2.2) (not_le.2 hN)
  · rcases generic hN hqr h2 with g2 | on2
    · rcases generic hN hrp h3 with g3 | on3
      · have h := tri_on hN hD on1.1 on1.2 g2 g3
        filter_upwards [h] with δ hδ
        rw [hδ, g_of_not_on (hnot g2), g_of_not_on (hnot g3)]
        ring
      · exact absurd (not_three_on hD on1.1 on1.2 on3.1) (not_le.2 hN)
    · exact absurd (not_three_on hD on1.1 on1.2 on2.2) (not_le.2 hN)

/-- Near a generic point `x` of the line, the points `x ± δ n` are off the line of the side. -/
private theorem side_ne {a b : ℝ × ℝ} {c τ : ℝ} (hab : a ≠ b) (hτ : τ ∉ Bad d c a b) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, cross a b (pt d c τ + δ • nrm d) ≠ 0 ∧
      cross a b (pt d c τ + δ • (-nrm d)) ≠ 0 := by
  rcases generic hN hab hτ with g1 | on1
  · filter_upwards [ev_sign a b (pt d c τ) (nrm d) g1, ev_sign a b (pt d c τ) (-nrm d) g1]
      with δ e e'
    exact ⟨e.2, e'.2⟩
  · have ht : dt d b - dt d a ≠ 0 := by
      intro ht
      exact hab (eq_of_coords hN (on1.1.trans on1.2.symm) (by linarith))
    have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := eventually_mem_nhdsWithin
    filter_upwards [hpos] with δ hδ
    obtain ⟨c1, c1'⟩ := cross_on hN on1.1 on1.2 τ δ
    rw [c1, c1']
    exact ⟨mul_ne_zero hδ.ne' ht, neg_ne_zero.2 (mul_ne_zero hδ.ne' ht)⟩

private theorem mem_seg {a b : ℝ × ℝ} {c τ : ℝ} (ha : det d a = c) (hb : det d b = c) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hτ : s * dt d a + t * dt d b = τ) :
    pt d c τ ∈ segment ℝ a b :=
  ⟨s, t, hs, ht, hst, eq_of_coords hN
    (by rw [det_comb, det_pt hN, ha, hb, ← add_mul, hst, one_mul])
    (by rw [dt_comb, dt_pt hN, hτ])⟩

/-- Where the signed indicator of a side is non-zero, the point lies on the side. -/
private theorem seg_of_g {a b : ℝ × ℝ} {c τ : ℝ} (hg : g d c a b τ ≠ 0) :
    pt d c τ ∈ segment ℝ a b := by
  by_cases hon : det d a = c ∧ det d b = c
  · by_cases h1 : dt d a < τ ∧ τ < dt d b
    · have hpos : 0 < dt d b - dt d a := by linarith [h1.1, h1.2]
      refine mem_seg hN hon.1 hon.2 ((dt d b - τ) / (dt d b - dt d a))
        ((τ - dt d a) / (dt d b - dt d a)) (div_nonneg (by linarith [h1.2]) hpos.le)
        (div_nonneg (by linarith [h1.1]) hpos.le) ?_ ?_
      · rw [← add_div, div_eq_one_iff_eq hpos.ne']; ring
      · field_simp; ring
    · by_cases h2 : dt d b < τ ∧ τ < dt d a
      · have hpos : 0 < dt d a - dt d b := by linarith [h2.1, h2.2]
        refine mem_seg hN hon.1 hon.2 ((τ - dt d b) / (dt d a - dt d b))
          ((dt d a - τ) / (dt d a - dt d b)) (div_nonneg (by linarith [h2.1]) hpos.le)
          (div_nonneg (by linarith [h2.2]) hpos.le) ?_ ?_
        · rw [← add_div, div_eq_one_iff_eq hpos.ne']; ring
        · field_simp; ring
      · exfalso
        apply hg
        simp only [g, hon, and_self, ↓reduceIte]
        rw [ind_neg h1, ind_neg h2, sub_self]
  · exact absurd (g_of_not_on hon τ) hg

/-- If a generic point of the line lies on a side, the side lies on the line and the point is
strictly between its end points. -/
private theorem on_of_mem_seg {a b : ℝ × ℝ} {c τ : ℝ} (hx : pt d c τ ∈ segment ℝ a b)
    (hτ : τ ∉ Bad d c a b) :
    det d a = c ∧ det d b = c ∧
      ((dt d a < τ ∧ τ < dt d b) ∨ (dt d b < τ ∧ τ < dt d a)) := by
  obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
  have h1 : s * det d a + t * det d b = c := by rw [← det_comb, hxe, det_pt hN]
  have h2 : s * dt d a + t * dt d b = τ := by rw [← dt_comb, hxe, dt_pt hN]
  have hτa : τ ≠ dt d a := fun h => hτ (Or.inl h)
  have hτb : τ ≠ dt d b := fun h => hτ (Or.inr (Or.inl h))
  have hs' : s = 1 - t := by linarith
  subst hs'
  have hcc : det d b = det d a := by
    by_contra hc
    apply hτ
    right; right
    refine ⟨hc, ?_⟩
    have hc' : det d b - det d a ≠ 0 := sub_ne_zero.2 hc
    have key : (τ - dt d a) * (det d b - det d a) = (dt d b - dt d a) * (c - det d a) := by
      rw [← h1, ← h2]; ring
    field_simp
    linarith
  have hca : det d a = c := by rw [hcc] at h1; linarith
  refine ⟨hca, hcc.trans hca, ?_⟩
  have e1 : τ - dt d a = t * (dt d b - dt d a) := by rw [← h2]; ring
  have e2 : dt d b - τ = (1 - t) * (dt d b - dt d a) := by rw [← h2]; ring
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hτa; linarith
  have ht1 : 1 - t ≠ 0 := by
    intro h
    apply hτb
    rw [h, zero_mul] at e2
    linarith
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hspos : 0 < 1 - t := lt_of_le_of_ne hs (Ne.symm ht1)
  rcases lt_trichotomy (dt d a) (dt d b) with hlt | heq | hgt
  · left
    have hk : 0 < dt d b - dt d a := by linarith
    have := mul_pos htpos hk
    have := mul_pos hspos hk
    constructor <;> linarith
  · exfalso
    apply hτa
    rw [heq, sub_self, mul_zero] at e1
    linarith
  · right
    have hk : 0 < dt d a - dt d b := by linarith
    have := mul_pos htpos hk
    have := mul_pos hspos hk
    constructor <;> nlinarith

/-- **The jump of the indicator of `S`** at a generic point of the line is the sum of the
signed indicators of the boundary sides on the line. -/
private theorem bdry_generic {S : Set (ℝ × ℝ)} {κ : Type*} [Fintype κ] {A B : κ → ℝ × ℝ}
    (hS : OrientedBoundary S A B) {c τ : ℝ} (hτ : ∀ k, τ ∉ Bad d c (A k) (B k))
    (huniq : ∀ j k, j ≠ k → ¬(pt d c τ ∈ segment ℝ (A j) (B j) ∧
      pt d c τ ∈ segment ℝ (A k) (B k))) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ind (pt d c τ + δ • nrm d ∈ S) - ind (pt d c τ + δ • (-nrm d) ∈ S)
      = ∑ k, g d c (A k) (B k) τ := by
  by_cases hex : ∃ k, pt d c τ ∈ segment ℝ (A k) (B k)
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨ha, hb, hbetw⟩ := on_of_mem_seg hN hk (hτ k)
    have hxa : pt d c τ ≠ A k := by
      intro h
      apply hτ k
      left
      have := congrArg (dt d) h
      rwa [dt_pt hN] at this
    have hxb : pt d c τ ≠ B k := by
      intro h
      apply hτ k
      right; left
      have := congrArg (dt d) h
      rwa [dt_pt hN] at this
    have hl := hS.left k (pt d c τ) hk hxa hxb (fun j hj hxj => huniq j k hj ⟨hxj, hk⟩)
    have hsum : ∑ j, g d c (A j) (B j) τ = g d c (A k) (B k) τ := by
      apply Finset.sum_eq_single k
      · intro j _ hj
        by_contra hg
        exact huniq j k hj ⟨seg_of_g hN hg, hk⟩
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsum]
    have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := eventually_mem_nhdsWithin
    filter_upwards [(tendsto_add_smul (pt d c τ) (nrm d)).eventually hl,
      (tendsto_add_smul (pt d c τ) (-nrm d)).eventually hl, hpos] with δ e e' hδ
    obtain ⟨c1, c1'⟩ := cross_on hN ha hb τ δ
    rw [c1] at e
    rw [c1'] at e'
    have hg : g d c (A k) (B k) τ = ind (dt d (A k) < τ ∧ τ < dt d (B k))
        - ind (dt d (B k) < τ ∧ τ < dt d (A k)) := by
      simp only [g, ha, hb, and_self, ↓reduceIte]
    rw [hg]
    rcases hbetw with hb1 | hb2
    · have hk' : 0 < dt d (B k) - dt d (A k) := by linarith [hb1.1, hb1.2]
      have hm := mul_pos hδ hk'
      rw [ind_pos (e.1 hm), ind_neg (e'.2 (by linarith)), ind_pos hb1,
        ind_neg (fun h => by linarith [h.1, h.2, hb1.1])]
    · have hk' : 0 < dt d (A k) - dt d (B k) := by linarith [hb2.1, hb2.2]
      have hm := mul_pos hδ hk'
      rw [ind_neg (e.2 (by nlinarith)), ind_pos (e'.1 (by nlinarith)), ind_pos hb2,
        ind_neg (fun h => by linarith [h.1, h.2, hb2.1])]
  · simp only [not_exists] at hex
    have hsum : ∑ j, g d c (A j) (B j) τ = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_contra hg
      exact hex k (seg_of_g hN hg)
    rw [hsum]
    rcases hS.off (pt d c τ) hex with hin | hout
    · filter_upwards [(tendsto_add_smul (pt d c τ) (nrm d)).eventually hin,
        (tendsto_add_smul (pt d c τ) (-nrm d)).eventually hin] with δ e e'
      rw [ind_pos e, ind_pos e', sub_self]
    · filter_upwards [(tendsto_add_smul (pt d c τ) (nrm d)).eventually hout,
        (tendsto_add_smul (pt d c τ) (-nrm d)).eventually hout] with δ e e'
      rw [ind_neg e, ind_neg e', sub_self]

end line

/-- At a point on no side line, the indicators of the triangles sum to the indicator of their
union. -/
private theorem sum_ind {ι : Type*} [Fintype ι] (p q r : ι → ℝ × ℝ)
    (hD : ∀ i, 0 < det (q i - p i) (r i - p i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (convexHull ℝ {p i, q i, r i}))
      (interior (convexHull ℝ {p j, q j, r j})))
    {S : Set (ℝ × ℝ)} (hU : (⋃ i, convexHull ℝ {p i, q i, r i}) = S) (y : ℝ × ℝ)
    (hy : ∀ i, cross (p i) (q i) y ≠ 0 ∧ cross (q i) (r i) y ≠ 0 ∧ cross (r i) (p i) y ≠ 0) :
    ∑ i, ind (y ∈ Tc (p i) (q i) (r i)) = ind (y ∈ S) := by
  have hTo : ∀ i, y ∈ Tc (p i) (q i) (r i) → y ∈ interior (convexHull ℝ {p i, q i, r i}) :=
    fun i h => To_subset_interior (hD i) ⟨lt_of_le_of_ne h.1 (hy i).1.symm,
      lt_of_le_of_ne h.2.1 (hy i).2.1.symm, lt_of_le_of_ne h.2.2 (hy i).2.2.symm⟩
  by_cases hyS : y ∈ S
  · have hyS' := hyS
    rw [← hU] at hyS'
    obtain ⟨i0, hi0⟩ := mem_iUnion.1 hyS'
    rw [Tc_eq_convexHull (hD i0)] at hi0
    rw [Finset.sum_eq_single i0, ind_pos hi0, ind_pos hyS]
    · intro j _ hj
      apply ind_neg
      intro hjm
      exact disjoint_left.1 (hdisj j i0 hj) (hTo j hjm) (hTo i0 hi0)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ind_neg hyS]
    apply Finset.sum_eq_zero
    intro i _
    apply ind_neg
    intro h
    apply hyS
    rw [← hU]
    exact mem_iUnion.2 ⟨i, by rw [Tc_eq_convexHull (hD i)]; exact h⟩

/-! ### Integration along the line -/

private theorem ind_eq_indicator (a b τ : ℝ) :
    ind (a < τ ∧ τ < b) = (Ioo a b).indicator (fun _ => (1 : ℝ)) τ := by
  by_cases h : a < τ ∧ τ < b
  · rw [ind_pos h, indicator_of_mem (mem_Ioo.2 h)]
  · rw [ind_neg h, indicator_of_notMem (fun h' => h (mem_Ioo.1 h'))]

private theorem integrable_ind (a b : ℝ) : Integrable (fun τ => ind (a < τ ∧ τ < b)) := by
  have h : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo a b) volume :=
    (continuous_const.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have h2 := h.integrable_indicator measurableSet_Ioo
  exact h2.congr (Eventually.of_forall (fun τ => (ind_eq_indicator a b τ).symm))

private theorem integral_ind (a b : ℝ) : ∫ τ, ind (a < τ ∧ τ < b) = max (b - a) 0 := by
  have e : (fun τ => ind (a < τ ∧ τ < b)) = (Ioo a b).indicator (fun _ => (1 : ℝ)) :=
    funext (ind_eq_indicator a b)
  rw [e, integral_indicator measurableSet_Ioo, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal']

private theorem integrable_g (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) : Integrable (g d c a b) := by
  by_cases hon : det d a = c ∧ det d b = c
  · have e : g d c a b
        = fun τ => ind (dt d a < τ ∧ τ < dt d b) - ind (dt d b < τ ∧ τ < dt d a) := by
      funext τ
      simp only [g, hon, and_self, ↓reduceIte]
    rw [e]
    exact (integrable_ind _ _).sub (integrable_ind _ _)
  · have e : g d c a b = fun _ => 0 := funext (g_of_not_on hon)
    rw [e]
    exact integrable_zero _ _ _

private theorem integral_g (d : ℝ × ℝ) (c : ℝ) (a b : ℝ × ℝ) : ∫ τ, g d c a b τ = mlev d c a b := by
  by_cases hon : det d a = c ∧ det d b = c
  · have e : g d c a b
        = fun τ => ind (dt d a < τ ∧ τ < dt d b) - ind (dt d b < τ ∧ τ < dt d a) := by
      funext τ
      simp only [g, hon, and_self, ↓reduceIte]
    rw [e, integral_sub (integrable_ind _ _) (integrable_ind _ _), integral_ind, integral_ind]
    simp only [mlev, hon, and_self, ↓reduceIte]
    rcases le_total (dt d a) (dt d b) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · have e : g d c a b = fun _ => 0 := funext (g_of_not_on hon)
    rw [e]
    simp [mlev, hon]

/-- **Balance on one line.**  The signed lengths of the triangle sides lying on the line
`det d · = c` sum to the signed lengths of the boundary sides lying on that line. -/
private theorem balance_level {ι κ : Type*} [Fintype ι] [Fintype κ] {S : Set (ℝ × ℝ)}
    {A B : κ → ℝ × ℝ} (hS : OrientedBoundary S A B) (p q r : ι → ℝ × ℝ)
    (hD : ∀ i, 0 < det (q i - p i) (r i - p i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (convexHull ℝ {p i, q i, r i}))
      (interior (convexHull ℝ {p j, q j, r j})))
    (hU : (⋃ i, convexHull ℝ {p i, q i, r i}) = S)
    {d : ℝ × ℝ} (hN : 0 < d.1 ^ 2 + d.2 ^ 2) (c : ℝ) :
    ∑ i, (mlev d c (p i) (q i) + mlev d c (q i) (r i) + mlev d c (r i) (p i))
      = ∑ k, mlev d c (A k) (B k) := by
  -- the exceptional parameters
  let Bset : Set ℝ := ((⋃ i, (Bad d c (p i) (q i) ∪ Bad d c (q i) (r i) ∪ Bad d c (r i) (p i)))
    ∪ (⋃ k, Bad d c (A k) (B k)))
    ∪ (⋃ j, ⋃ k, {τ | j ≠ k ∧ pt d c τ ∈ segment ℝ (A j) (B j) ∩ segment ℝ (A k) (B k)})
  have hinj : Function.Injective (pt d c) := by
    intro τ τ' h
    have := congrArg (dt d) h
    rwa [dt_pt hN, dt_pt hN] at this
  have hfin : Bset.Finite := by
    refine ((Set.finite_iUnion (fun i => ((Bad_finite _ _ _ _).union (Bad_finite _ _ _ _)).union
      (Bad_finite _ _ _ _))).union (Set.finite_iUnion (fun k => Bad_finite _ _ _ _))).union
      (Set.finite_iUnion (fun j => Set.finite_iUnion (fun k => ?_)))
    by_cases hjk : j = k
    · apply Set.finite_empty.subset
      intro τ hτ
      exact absurd hjk hτ.1
    · apply ((hS.fin j k hjk).preimage hinj.injOn).subset
      intro τ hτ
      exact hτ.2
  -- pointwise identity at generic parameters
  have hpoint : ∀ τ, τ ∉ Bset →
      ∑ i, (g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ)
        = ∑ k, g d c (A k) (B k) τ := by
    intro τ hτ
    have hT : ∀ i, τ ∉ Bad d c (p i) (q i) ∧ τ ∉ Bad d c (q i) (r i) ∧
        τ ∉ Bad d c (r i) (p i) := by
      intro i
      refine ⟨fun h => hτ ?_, fun h => hτ ?_, fun h => hτ ?_⟩
      · exact Or.inl (Or.inl (mem_iUnion.2 ⟨i, Or.inl (Or.inl h)⟩))
      · exact Or.inl (Or.inl (mem_iUnion.2 ⟨i, Or.inl (Or.inr h)⟩))
      · exact Or.inl (Or.inl (mem_iUnion.2 ⟨i, Or.inr h⟩))
    have hBk : ∀ k, τ ∉ Bad d c (A k) (B k) :=
      fun k h => hτ (Or.inl (Or.inr (mem_iUnion.2 ⟨k, h⟩)))
    have huniq : ∀ j k, j ≠ k → ¬(pt d c τ ∈ segment ℝ (A j) (B j) ∧
        pt d c τ ∈ segment ℝ (A k) (B k)) :=
      fun j k hjk h => hτ (Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨k, hjk, h⟩⟩))
    have E1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i, ind (pt d c τ + δ • nrm d ∈ Tc (p i) (q i) (r i))
        - ind (pt d c τ + δ • (-nrm d) ∈ Tc (p i) (q i) (r i))
          = g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ :=
      eventually_all.2 (fun i => tri_generic hN (hD i) (hT i).1 (hT i).2.1 (hT i).2.2)
    have E2 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i,
        ((cross (p i) (q i) (pt d c τ + δ • nrm d) ≠ 0 ∧
          cross (p i) (q i) (pt d c τ + δ • (-nrm d)) ≠ 0) ∧
        (cross (q i) (r i) (pt d c τ + δ • nrm d) ≠ 0 ∧
          cross (q i) (r i) (pt d c τ + δ • (-nrm d)) ≠ 0)) ∧
        (cross (r i) (p i) (pt d c τ + δ • nrm d) ≠ 0 ∧
          cross (r i) (p i) (pt d c τ + δ • (-nrm d)) ≠ 0) :=
      eventually_all.2 (fun i =>
        ((side_ne hN (ne_of_det_pos (hD i)).1 (hT i).1).and
          (side_ne hN (ne_of_det_pos (hD i)).2.1 (hT i).2.1)).and
          (side_ne hN (ne_of_det_pos (hD i)).2.2 (hT i).2.2))
    have E3 := bdry_generic hN hS hBk huniq
    obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := ((E1.and E2).and E3).exists
    calc ∑ i, (g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ)
        = ∑ i, (ind (pt d c τ + δ • nrm d ∈ Tc (p i) (q i) (r i))
          - ind (pt d c τ + δ • (-nrm d) ∈ Tc (p i) (q i) (r i))) :=
          Finset.sum_congr rfl (fun i _ => (h1 i).symm)
      _ = ind (pt d c τ + δ • nrm d ∈ S) - ind (pt d c τ + δ • (-nrm d) ∈ S) := by
          rw [Finset.sum_sub_distrib,
            sum_ind p q r hD hdisj hU _ (fun i => ⟨(h2 i).1.1.1, (h2 i).1.2.1, (h2 i).2.1⟩),
            sum_ind p q r hD hdisj hU _ (fun i => ⟨(h2 i).1.1.2, (h2 i).1.2.2, (h2 i).2.2⟩)]
      _ = ∑ k, g d c (A k) (B k) τ := h3
  -- integrate
  have hae : (fun τ => ∑ i, (g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ))
      =ᵐ[volume] (fun τ => ∑ k, g d c (A k) (B k) τ) := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ (hfin.measure_zero volume)
    intro τ hτ
    by_contra hnot
    exact hτ (hpoint τ hnot)
  have hint := integral_congr_ae hae
  have hI3 : ∀ i, Integrable (fun τ => g d c (p i) (q i) τ + g d c (q i) (r i) τ
      + g d c (r i) (p i) τ) := fun i =>
    ((integrable_g d c (p i) (q i)).add (integrable_g d c (q i) (r i))).add
      (integrable_g d c (r i) (p i))
  have hI2 : ∀ i, Integrable (fun τ => g d c (p i) (q i) τ + g d c (q i) (r i) τ) := fun i =>
    (integrable_g d c (p i) (q i)).add (integrable_g d c (q i) (r i))
  have hL : ∫ τ, ∑ i, (g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ)
      = ∑ i, (mlev d c (p i) (q i) + mlev d c (q i) (r i) + mlev d c (r i) (p i)) := by
    rw [integral_finsetSum Finset.univ
      (f := fun i τ => g d c (p i) (q i) τ + g d c (q i) (r i) τ + g d c (r i) (p i) τ)
      (fun i _ => hI3 i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_add (hI2 i) (integrable_g d c (r i) (p i)),
      integral_add (integrable_g d c (p i) (q i)) (integrable_g d c (q i) (r i)),
      integral_g, integral_g, integral_g]
  have hR : ∫ τ, ∑ k, g d c (A k) (B k) τ = ∑ k, mlev d c (A k) (B k) := by
    rw [integral_finsetSum Finset.univ (f := fun k τ => g d c (A k) (B k) τ)
      (fun k _ => integrable_g d c (A k) (B k))]
    exact Finset.sum_congr rfl (fun k _ => integral_g _ _ _ _)
  rw [← hL, ← hR]
  exact hint

/-! ### Summing over the lines -/

/-- The signed length (times `|d|`) of `a → b` if it is parallel to `d`, and `0` otherwise. -/
private def mpar (d a b : ℝ × ℝ) : ℝ := if det d b = det d a then dt d b - dt d a else 0

private theorem sum_mlev (d a b : ℝ × ℝ) (C : Finset ℝ) (ha : det d a ∈ C) :
    ∑ c ∈ C, mlev d c a b = mpar d a b := by
  rw [Finset.sum_eq_single (det d a)]
  · simp [mlev, mpar]
  · intro c _ hc
    simp only [mlev]
    rw [ite_eq_right_iff]
    intro h
    exact absurd h.1.symm hc
  · intro h
    exact absurd ha h

private theorem par_eq {d : ℝ × ℝ} (hN : 0 < d.1 ^ 2 + d.2 ^ 2) (a b : ℝ × ℝ) :
    par d (b - a) = (mpar d a b / (d.1 ^ 2 + d.2 ^ 2)) • d := by
  have hdet : det d (b - a) = det d b - det d a := by
    simp only [det, Prod.fst_sub, Prod.snd_sub]; ring
  by_cases h : det d b = det d a
  · have h0 : det d (b - a) = 0 := by rw [hdet, h, sub_self]
    simp only [par, h0, ↓reduceIte, mpar, h]
    have hN' := hN.ne'
    simp only [det, Prod.fst_sub, Prod.snd_sub] at h0
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul, dt]
      field_simp
      linear_combination (-d.2) * h0
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul, dt]
      field_simp
      linear_combination d.1 * h0
  · have h0 : det d (b - a) ≠ 0 := by rw [hdet]; exact sub_ne_zero.2 h
    simp [par, h0, mpar, h]

/-- **Lemma 4.1 (Balance).**  Let `S ⊆ ℝ²` lie on the left of its oriented boundary, which
consists of the sides `A k → B k`, and let `S` be dissected into the counter-clockwise triangles
`p i, q i, r i` (pairwise disjoint interiors, union `S`).  Then for every direction `d ≠ 0`, the
side vectors of the triangles parallel to `d` sum to the sum of the boundary vectors `B k - A k`
parallel to `d`. -/
theorem balance {ι κ : Type*} [Fintype ι] [Fintype κ] {S : Set (ℝ × ℝ)} {A B : κ → ℝ × ℝ}
    (hS : OrientedBoundary S A B) (p q r : ι → ℝ × ℝ)
    (hD : ∀ i, 0 < det (q i - p i) (r i - p i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (convexHull ℝ {p i, q i, r i}))
      (interior (convexHull ℝ {p j, q j, r j})))
    (hU : (⋃ i, convexHull ℝ {p i, q i, r i}) = S) (d : ℝ × ℝ) (hd : d ≠ 0) :
    ∑ i, (par d (q i - p i) + par d (r i - q i) + par d (p i - r i))
      = ∑ k, par d (B k - A k) := by
  classical
  have hN : 0 < d.1 ^ 2 + d.2 ^ 2 := sq_add_sq_pos hd
  let C : Finset ℝ := Finset.univ.image (fun i => det d (p i)) ∪
    Finset.univ.image (fun i => det d (q i)) ∪ Finset.univ.image (fun i => det d (r i)) ∪
    Finset.univ.image (fun k => det d (A k))
  have hCp : ∀ i, det d (p i) ∈ C := fun i => by
    simp only [C, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))
  have hCq : ∀ i, det d (q i) ∈ C := fun i => by
    simp only [C, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))
  have hCr : ∀ i, det d (r i) ∈ C := fun i => by
    simp only [C, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨i, rfl⟩)
  have hCA : ∀ k, det d (A k) ∈ C := fun k => by
    simp only [C, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨k, rfl⟩
  have hscal : ∑ i, (mpar d (p i) (q i) + mpar d (q i) (r i) + mpar d (r i) (p i))
      = ∑ k, mpar d (A k) (B k) := by
    calc ∑ i, (mpar d (p i) (q i) + mpar d (q i) (r i) + mpar d (r i) (p i))
        = ∑ i, ∑ c ∈ C, (mlev d c (p i) (q i) + mlev d c (q i) (r i)
            + mlev d c (r i) (p i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_mlev _ _ _ _ (hCp i),
            sum_mlev _ _ _ _ (hCq i), sum_mlev _ _ _ _ (hCr i)]
      _ = ∑ c ∈ C, ∑ i, (mlev d c (p i) (q i) + mlev d c (q i) (r i)
            + mlev d c (r i) (p i)) := Finset.sum_comm
      _ = ∑ c ∈ C, ∑ k, mlev d c (A k) (B k) :=
          Finset.sum_congr rfl (fun c _ => balance_level hS p q r hD hdisj hU hN c)
      _ = ∑ k, ∑ c ∈ C, mlev d c (A k) (B k) := Finset.sum_comm
      _ = ∑ k, mpar d (A k) (B k) :=
          Finset.sum_congr rfl (fun k _ => sum_mlev _ _ _ _ (hCA k))
  simp only [par_eq hN]
  rw [← Finset.sum_smul, ← Finset.sum_div]
  simp only [← add_smul, ← add_div]
  rw [← Finset.sum_smul, ← Finset.sum_div, hscal]

end

end Stein
