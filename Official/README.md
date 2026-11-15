# Problem 67: the official Lean statement of Monsky's theorem

This folder proves the organisers' official Lean statement of Problem 67,

```
theorem Mathathon.P67.Monsky (n : ℕ) :
    (∃ S : Finset Triangle, closed_hull unit_square = ⋃ Δ ∈ S, closed_hull Δ ∧
      Set.PairwiseDisjoint (S : Set Triangle) open_hull ∧
      (∀ Δ₁ ∈ S, ∀ Δ₂ ∈ S, volume (open_hull Δ₁) = volume (open_hull Δ₂)) ∧ S.card = n)
    ↔ (n ≠ 0 ∧ Even n)
```

as a corollary of the team's own Lean proof of Stein's conjecture in [`../Lean`](../Lean).

## Layout

The folder mirrors `problems_ai/lean` of the official repository
<https://github.com/SAIRcompetition/mathathon-judge> (same package name, library name, file
name, namespace, toolchain and Mathlib revision).

| file | content |
|---|---|
| `MathathonProblems/P67_Monsky.lean` | the official file with the proof filled in |
| `MathathonProblems.lean` | library root (imports the file above) |
| `AxiomCheck.lean` | `#check` and `#print axioms` of `Mathathon.P67.Monsky` |
| `reference/P67_Monsky.lean.official` | unmodified copy of the official file, for comparison (not compiled) |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | as in the official repository, plus the dependency on `../Lean` |
| `lean-check-output.txt` | output of our last build and axiom check |

## Relation to the official file

The official file was downloaded from
`problems_ai/lean/MathathonProblems/P67_Monsky.lean` (repository commit `4d6098d`, file last
changed in commit `e68bb38`; sha256 `b4db5fd576358017f9100e1ad87296463d4aec51061437c90ec74d48aee30433`). `diff reference/P67_Monsky.lean.official
MathathonProblems/P67_Monsky.lean` shows exactly three changes, all additions:

1. the line `import Stein.Main` after `import Mathlib`;
2. a block of private auxiliary definitions and lemmas (`section Auxiliary`) between the
   definition of `unit_square` and the theorem;
3. `sorry` is replaced by the proof.

The header comment, the notations, `open Classical`, the namespace, the six definitions (`v`,
`closed_simplex`, `open_simplex`, `closed_hull`, `open_hull`, `unit_square`) and the statement of
`Monsky` are unchanged, character for character.

## What is used from the team library

The file imports `Stein.Main` from the package `Stein` (`../Lean`) and uses

| declaration | role |
|---|---|
| `Stein.monsky` | Monsky's theorem for `Set.Icc (0 : ℝ × ℝ) 1`: a dissection into triangles of equal area has an even number of triangles. This is the mathematical content of the direction "⟹ `Even n`". |
| `Stein.IsDissection`, `Stein.IsTriangle` | the hypotheses of `Stein.monsky` |
| `Stein.volume_triangle`, `Stein.det` | area of a triangle; used to show that the `2 k` triangles of the explicit dissection have the same area |

Nothing from an existing Lean proof of Monsky's theorem (in particular nothing from
`dhyan-aranha/Monsky`, the source of the official statement) was used or consulted.

## Proof

*Direction "⟹".* Let `S` be as in the statement. The coordinate map `toProd : ℝ² → ℝ × ℝ` is a
linear homeomorphism that preserves Lebesgue measure. `closed_hull Δ` is the convex hull of the
three vertices. The square has area `1`, so some closed triangle of `S` has positive area. A
closed triangle with affinely dependent vertices is a null set, and for affinely independent
vertices the interior of `closed_hull Δ` is contained in `open_hull Δ`, so that `open_hull Δ` and
`closed_hull Δ` always have the same area. As all open triangles have the same area, all
triangles of `S` are non-degenerate; in particular `S ≠ ∅`, so `n ≠ 0`. The sets
`toProd '' closed_hull Δ` (`Δ ∈ S`) then form a dissection of `[0,1]²` in the sense of
`Stein.IsDissection` (their interiors are disjoint because the open triangles are), with equal
areas, and `Stein.monsky` gives `Even n`.

*Direction "⟸".* For `n = 2 k`, `k ≠ 0`, the square is cut into the `k` vertical strips
`[j/k, (j+1)/k] × [0,1]` and each strip into two triangles by a diagonal (`stripTri`,
`dissection`). Membership in the closed and open triangles is described by explicit barycentric
coordinates (`bary`), which gives the covering and the disjointness; all areas are `1/(2k)`;
the `2 k` triangles are different because they are non-empty and pairwise disjoint.

## Build

Lean `v4.35.0` and Mathlib `v4.35.0` (rev `56a0058`), the versions of the official repository and
of the rules; all package revisions in `lake-manifest.json` are those of the official manifest.
The team library `../Lean` is required as a local path dependency, so this folder has to stay
next to `Lean/`.

```
cd Official
lake exe cache get              # Mathlib build cache (do not run `lake update`)
lake build                      # builds ../Lean (if not built yet) and MathathonProblems
lake env lean AxiomCheck.lean   # prints the statement and its axioms
```

Expected: `Build completed successfully`, and

```
'Mathathon.P67.Monsky' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry`, no `native_decide` and no `axiom` in the file. Our last run is recorded in
`lean-check-output.txt`.
