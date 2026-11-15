import Stein.Basic

/-!
# The arithmetic input (paper, §2)

Lemma 2.1 of the paper: every field of characteristic `0` has a valuation with `v(2) > 0`.
In Mathlib's multiplicative convention this reads `v 2 < 1`.
-/

namespace Stein

/-- **Lemma 2.1 (existence).** Every field `K` of characteristic `0` has a valuation ring `O`
whose valuation satisfies `v(2) > 0` (multiplicatively: `O.valuation 2 < 1`), i.e. `1/2 ∉ O`.

The paper gives a Zorn-free construction for countable `K`; here we use instead Mathlib's
general existence theorem for valuation subrings dominating a local subring
(`Ideal.image_subset_nonunits_valuationSubring`, Chevalley's extension theorem, proved with
Zorn's lemma), applied to the image of `ℤ` in `K` and its proper ideal `(2)`. -/
theorem exists_valuation_two_pos (K : Type*) [Field K] [CharZero K] :
    ∃ O : ValuationSubring K, O.valuation 2 < 1 := by
  -- the image of `ℤ` in `K`
  let A : Subring K := (Int.castRingHom K).range
  have h2 : (2 : K) ∈ A := ⟨2, by simp⟩
  let I : Ideal A := Ideal.span {⟨2, h2⟩}
  -- `(2)` is a proper ideal of it, because `2 n = 1` has no solution in `ℤ`
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := by rw [h]; trivial
    obtain ⟨⟨a, n, rfl⟩, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have h3 : ((n * 2 : ℤ) : K) = ((1 : ℤ) : K) := by
      have := congrArg Subtype.val ha
      simpa using this
    have h4 : n * 2 = 1 := Int.cast_injective h3
    omega
  obtain ⟨O, -, hO⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have h : (2 : K) ∈ O.nonunits := hO ⟨⟨2, h2⟩, Ideal.subset_span rfl, rfl⟩
  exact ⟨O, h⟩

end Stein
