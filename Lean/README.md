# Stein's conjecture and Monsky's theorem in Lean 4

A Lean 4 / Mathlib formalisation of the paper *"Monsky's theorem and Stein's conjecture: a short
proof by merging parallel sides"*.  The project depends only on Mathlib.

**Status.** Everything listed below is proved.  The project builds with no `sorry`, no
`native_decide` and no `axiom`; `#print axioms` of every headline declaration reports a subset of
`[propext, Classical.choice, Quot.sound]` (file `Stein/Axioms.lean`, recorded output in
`lean-check-output.txt`).

## Build

Lean `v4.35.0` (`lean-toolchain`), Mathlib `v4.35.0` (pinned in `lakefile.toml` and
`lake-manifest.json`).

```
lake exe cache get && lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` then compiles this project (a
few minutes) and ends with `Build completed successfully`.  Do not run `lake update`.

**Axioms.**  `Stein/Axioms.lean` contains one `#print axioms` command for every headline
declaration; it is part of the default target, so `lake build` prints lines of the form

```
info: Stein/Axioms.lean:…: 'Stein.stein_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`lake build Stein.Axioms` prints them again on demand; `lean-check-output.txt` is a recorded
run).  To check for `sorry`: `grep -rn "sorry\|native_decide\|^axiom" Stein Stein.lean` returns
nothing.

## What is proved

All names are in the namespace `Stein`; the polygon part is in `Stein.Polygon`.  `volume` is
`MeasureTheory.volume` on `ℝ × ℝ`, i.e. two-dimensional Lebesgue measure: the areas in the
statements are the true areas.

**Stein's conjecture** (Corollary 1.3; `Stein.stein_conjecture`, `Stein.stein_conjecture_fin`).
Let `P` be a simple polygon which is *special*: for every direction, the side vectors of `P`
parallel to that direction sum to zero.  If the region bounded by `P` is dissected into finitely
many triangles of equal area, then the number of triangles is even.

```lean
theorem Stein.stein_conjecture (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P)
    (hsp : SpecialPolygon P)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even (Fintype.card ι)

theorem Stein.stein_conjecture_fin (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P)
    (hsp : SpecialPolygon P)
    {n : ℕ} (T : Fin n → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (heq : ∀ i, volume (T i) = volume (region P) / n) : Even n
```

**Monsky's theorem** (`Stein.monsky`, `Stein.monsky_fin`).  The unit square cannot be dissected
into an odd number of triangles of equal area.

```lean
theorem Stein.monsky {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ))
    (hT : IsDissection (Set.Icc (0 : ℝ × ℝ) 1) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even (Fintype.card ι)

theorem Stein.monsky_fin {n : ℕ} (T : Fin n → Set (ℝ × ℝ))
    (hT : IsDissection (Set.Icc (0 : ℝ × ℝ) 1) T)
    (heq : ∀ i j, volume (T i) = volume (T j)) : Even n
```

**Main Theorem** (Theorem 1.2; `Stein.main_theorem`).  Let `P` be a special simple polygon,
dissected into triangles `T i` whose vertices have coordinates in a subfield `K` of `ℝ`, and let
`v` be a valuation on `K`.  Then `v(2 Area P) ≥ v(2) + min_i v(2 Area T_i)` (additive notation).

```lean
theorem Stein.main_theorem (P : Fin (m + 3) → ℝ × ℝ) (hP : SimplePolygon P)
    (hsp : SpecialPolygon P)
    {ι : Type*} [Fintype ι] (T : ι → Set (ℝ × ℝ)) (hT : IsDissection (region P) T)
    (K : Subfield ℝ) (hK : ∀ i, IsTriangleOver K (T i))
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (γ : Γ₀)
    (a : ι → K) (ha : ∀ i, (a i : ℝ) = 2 * (volume (T i)).toReal) (hγ : ∀ i, v (a i) ≤ γ)
    (a₀ : K) (ha₀ : (a₀ : ℝ) = 2 * (volume (region P)).toReal) :
    v a₀ ≤ v 2 * γ
```

(In the sources the line breaks differ slightly; the statements are these.)

### Valuations: Mathlib's convention versus the paper's

Mathlib's `Valuation K Γ₀` is *multiplicative*: `v : K → Γ₀` into a linearly ordered commutative
group with zero, `v 0 = 0`, `v (x * y) = v x * v y`, `v (x + y) ≤ max (v x) (v y)`.  The paper's
additive valuation `w` corresponds to `v = "exp(-w)"`, so every inequality is reversed and sums
become products:

| paper (additive) | Lean (multiplicative) |
|---|---|
| `w(x) ≥ ν` | `v x ≤ γ` |
| `w(2) > 0` (i.e. `1/2 ∉ O`) | `v 2 < 1` |
| `w(x) = ∞ ⇔ x = 0` | `v x = 0 ↔ x = 0` |
| `w(S) ≥ w(2) + ν` | `v S ≤ v 2 * γ` |
| `w(2 Area P) ≥ w(2) + min_i w(2 Area T_i)` | `(∀ i, v (a i) ≤ γ) → v a₀ ≤ v 2 * γ` (take `γ = max_i v (a i)`) |
| "`u` is at least as long as `w`": `w(u) ≤ w(w)` | `vnorm v w ≤ vnorm v u`, where `vnorm v w = max (v w.1) (v w.2)` |

## Definitions used in the headline statements

Exact Lean text (docstrings omitted; `m : ℕ` is an implicit variable).

```lean
-- Stein/Basic.lean
def det {K : Type*} [CommRing K] (a b : K × K) : K := a.1 * b.2 - a.2 * b.1

def par {K : Type*} [CommRing K] [DecidableEq K] (d w : K × K) : K × K :=
  if det d w = 0 then w else 0

def cross (a b x : ℝ × ℝ) : ℝ := (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)

structure OrientedBoundary (S : Set (ℝ × ℝ)) {κ : Type*} (A B : κ → ℝ × ℝ) : Prop where
  off : ∀ x, (∀ k, x ∉ segment ℝ (A k) (B k)) →
    (∀ᶠ y in 𝓝 x, y ∈ S) ∨ (∀ᶠ y in 𝓝 x, y ∉ S)
  left : ∀ k x, x ∈ segment ℝ (A k) (B k) → x ≠ A k → x ≠ B k →
    (∀ j, j ≠ k → x ∉ segment ℝ (A j) (B j)) →
    ∀ᶠ y in 𝓝 x, (0 < cross (A k) (B k) y → y ∈ S) ∧ (cross (A k) (B k) y < 0 → y ∉ S)
  fin : ∀ j k, j ≠ k → (segment ℝ (A j) (B j) ∩ segment ℝ (A k) (B k)).Finite

-- Stein/Polygon/Winding.lean, Stein/Polygon/Region.lean   (namespace Stein.Polygon)
def toC (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

def side (v : Fin (m + 3) → ℝ × ℝ) (k : Fin (m + 3)) : Set (ℝ × ℝ) :=
  segment ℝ (v k) (v (k + 1))

def boundary (v : Fin (m + 3) → ℝ × ℝ) : Set (ℝ × ℝ) := ⋃ k, side v k

structure SimplePolygon (v : Fin (m + 3) → ℝ × ℝ) : Prop where
  inj : Function.Injective v
  meet : ∀ j k, j ≠ k → ∀ x, x ∈ side v j → x ∈ side v k →
    (k = j + 1 ∧ x = v k) ∨ (j = k + 1 ∧ x = v j)

def windingNumber (v : Fin (m + 3) → ℝ × ℝ) (x : ℝ × ℝ) : ℤ :=
  round ((∑ k, Complex.arg ((toC (v (k + 1)) - toC x) / (toC (v k) - toC x))) / (2 * Real.pi))

def region (v : Fin (m + 3) → ℝ × ℝ) : Set (ℝ × ℝ) :=
  boundary v ∪ {x | windingNumber v x ≠ 0}

-- Stein/Geometry/Dissection.lean
def IsTriangle (T : Set (ℝ × ℝ)) : Prop :=
  ∃ p q r : ℝ × ℝ, ¬Collinear ℝ {p, q, r} ∧ T = convexHull ℝ {p, q, r}

def emb (K : Subfield ℝ) : K × K →+ ℝ × ℝ :=
  AddMonoidHom.prodMap (K.subtype : K →+ ℝ) (K.subtype : K →+ ℝ)

def IsTriangleOver (K : Subfield ℝ) (T : Set (ℝ × ℝ)) : Prop :=
  ∃ p q r : K × K, ¬Collinear ℝ {emb K p, emb K q, emb K r} ∧
    T = convexHull ℝ {emb K p, emb K q, emb K r}

structure IsDissection {ι : Type*} (S : Set (ℝ × ℝ)) (T : ι → Set (ℝ × ℝ)) : Prop where
  triangle : ∀ i, IsTriangle (T i)
  disjoint : ∀ i j, i ≠ j → Disjoint (interior (T i)) (interior (T j))
  union : (⋃ i, T i) = S

def Special {κ : Type*} [Fintype κ] (A B : κ → ℝ × ℝ) : Prop :=
  ∀ d : ℝ × ℝ, d ≠ 0 → ∑ k, par d (B k - A k) = 0

-- Stein/Main.lean
def SpecialPolygon (P : Fin (m + 3) → ℝ × ℝ) : Prop :=
  ∀ d : ℝ × ℝ, d ≠ 0 → ∑ k, par d (P (k + 1) - P k) = 0

-- Stein/Algebra/Sequences.lean   (K a commutative ring; for `Flat`, K a field)
abbrev sigma (c : List (K × K)) : K × K := c.sum

def bracket : List (K × K) → K
  | [] => 0
  | a :: c => det a c.sum + bracket c

def sideSeq (p q r : K × K) : List (K × K) := [q - p, r - q, p - r]

def S (F : List (List (K × K))) : K := (F.map bracket).sum

def Closed (F : List (List (K × K))) : Prop := ∀ c ∈ F, c.sum = 0

def Balanced [DecidableEq K] (F : List (List (K × K))) : Prop :=
  ∀ d : K × K, d ≠ 0 → (F.flatten.map (par d)).sum = 0

def Flat (v : Valuation K Γ₀) (γ : Γ₀) (F : List (List (K × K))) : Prop :=
  ∀ c ∈ F, ∀ w ∈ c, ∀ w' ∈ c, v (det w w') ≤ γ

-- Stein/Polygon/PolyInterior.lean, Stein/Polygon/Orientation.lean   (namespace Stein.Polygon)
def polyCurve {n : ℕ} [NeZero n] (v : Fin n → ℂ) : Set ℂ :=
  ⋃ k, segment ℝ (v k) (v (k + 1))

def polyInterior {n : ℕ} [NeZero n] (v : Fin n → ℂ) : Set ℂ :=
  {p | p ∉ polyCurve v ∧ Bornology.IsBounded (connectedComponentIn (polyCurve v)ᶜ p)}

def shoelace (v : Fin (m + 3) → ℝ × ℝ) : ℝ := ∑ k, det (v k) (v (k + 1))
```

In words:

* A polygon with `m + 3` vertices is a map `P : Fin (m + 3) → ℝ × ℝ`; the successor `k + 1` in
  `Fin (m + 3)` is cyclic, so the sides are the segments `P k → P (k + 1)`.
* `SimplePolygon P`: the vertices are pairwise distinct and two different sides have no common
  point, except that consecutive sides share exactly their common vertex.  (Consecutive sides
  may be collinear.)
* `windingNumber P x`: the sum of the signed angles in `(-π, π]` under which the sides are seen
  from `x`, divided by `2π`, points being read as complex numbers; `region P` is the curve
  together with the points of non-zero winding number.  That this is the closed region bounded by
  the curve in every usual sense is proved, see "The region bounded by a simple polygon" below.
* `SpecialPolygon P`: for every direction `d ≠ 0`, the side vectors `P (k+1) - P k` parallel to
  `d` sum to `0` (the condition is independent of the orientation).
* `IsDissection S T`: every `T i` is a non-degenerate closed triangle, different triangles have
  disjoint interiors, and the union of the triangles is `S`.  Vertices of one triangle may lie in
  the interior of a side of another one.
* `OrientedBoundary S A B`: "`S` lies on the left of its oriented boundary `A k → B k`": a point
  on no side has a neighbourhood inside `S` or a neighbourhood outside `S`; near a point of
  exactly one side, other than its end points, `S` contains the points strictly on the left of the
  side and none strictly on its right; two different sides have finitely many common points.
* `bracket c` is the paper's `[c] = Σ_{i<j} det (c_i, c_j)`, `sigma c = c.sum` is `σ(c)`; a
  *family* is a list of sequences; `S F = Σ_{c ∈ F} [c]`; `Closed`: every sequence has sum `0`;
  `Flat v γ`: `v (det w w') ≤ γ` for entries `w, w'` of the same sequence (the paper's "ν-flat");
  `Balanced`: for every direction, the entries of the family parallel to it sum to `0`.

## Paper statement ↔ Lean declaration

| paper | Lean declaration (namespace `Stein`) | file | remarks |
|---|---|---|---|
| Lemma 2.1 (a valuation with `v(2) > 0`) | `exists_valuation_two_pos (K) [Field K] [CharZero K] : ∃ O : ValuationSubring K, O.valuation 2 < 1` | `Algebra/Valuation.lean` | for every field of characteristic 0; proved with Mathlib's existence theorem for valuation subrings (Chevalley; Zorn's lemma), see difference 3 below |
| §3, formula (1): `[cc'] = [c] + [c'] + det(σc, σc')` | `bracket_append` | `Algebra/Sequences.lean` | any commutative ring |
| Lemma 3.1 (a) Join | `bracket_join` | `Algebra/Sequences.lean` | |
| Lemma 3.1 (b) Swap | `bracket_swap`, `sum_swap`; block version `bracket_move` | `Algebra/Sequences.lean` | explicit sign: `[A p q B] = [A q p B] + 2 det (p, q)` |
| Lemma 3.1 (c) Add | `bracket_add`, `sum_add` | `Algebra/Sequences.lean` | `[A p q B] = [A (p+q) B] + det (p, q)` |
| formula (2), side sequence of a triangle | `sum_sideSeq`, `bracket_sideSeq`, `det_sideSeq` | `Algebra/Sequences.lean` | `det_sideSeq` has the third case `det w w' = 0` (for `w = w'`), implicit in the paper |
| Definition 3.2 (family, `S(F)`, ν-flat, balanced) | `S`, `Closed`, `Flat`, `Balanced` | `Algebra/Sequences.lean` | "on the line `L`" is `det d w = 0` for a direction vector `d ≠ 0` of `L` |
| Lemma 4.1 (Balance), first sentence | `balance` | `Geometry/Balance.lean` | stated for any set `S` with `OrientedBoundary S A B`; different proof, see difference 4 below |
| Lemma 4.1, second sentence (special ⟹ balanced) | `balanced_of_special` | `Geometry/Dissection.lean` | |
| "a polygon lies on the left of its oriented boundary" (used tacitly) | `Polygon.region_orientedBoundary (v) (hv : SimplePolygon v) : OrientedBoundary (region v) v (fun k => v (k + 1)) ∨ OrientedBoundary (region v) (fun k => v (k + 1)) v` | `Polygon/Region.lean` | first case: counter-clockwise polygon, second: clockwise |
| Lemma 5.1 (Lemma T) | `lemma_T` | `Algebra/TheoremM.lean` | |
| Theorem 5.2 (Theorem M) | `theorem_M [DecidableEq K] (v : Valuation K Γ₀) (γ : Γ₀) (F : List (List (K × K))) (hc : Closed F) (hf : Flat v γ F) (hb : Balanced F) : v (S F) ≤ v 2 * γ` | `Algebra/TheoremM.lean` | any field, any valuation; induction on the number of entries as in the paper; `γ = 0` (the paper's `ν = ∞`) is allowed |
| "`[t] = 2 Area T`", "`S = 2 Area P`" | `volume_triangle (p q r) : volume (convexHull ℝ {p, q, r}) = ENNReal.ofReal (\|det (q - p) (r - p)\| / 2)`, `IsDissection.volume_eq_sum : volume S = ∑ i, volume (T i)` | `Geometry/Triangle.lean`, `Geometry/Dissection.lean` | areas are Lebesgue measure |
| Theorem 1.2 (Main Theorem) | `main_theorem`; `main_theorem_of_orientedBoundary` (any `S` on the left of its boundary); `main_theorem_square` | `Main.lean`, `Geometry/Dissection.lean` | see differences 5, 6 below |
| Corollary 1.3 (Stein's conjecture) | `stein_conjecture`, `stein_conjecture_fin`; `stein_conjecture_of_orientedBoundary` | `Main.lean`, `Geometry/Dissection.lean` | proved with `K = ℝ` and Lemma 2.1 for `ℝ` instead of `K = ℚ(coordinates)` |
| Corollary 1.3 (Monsky's theorem) | `monsky`, `monsky_fin` | `Main.lean` | the square is `Set.Icc (0 : ℝ × ℝ) 1`; deduced from `square_boundary`, `square_special` (`Geometry/Square.lean`), without the polygon part |

## The region bounded by a simple polygon

`region v` is defined through the winding number.  The following theorems (namespace
`Stein.Polygon`, `v : Fin (m + 3) → ℝ × ℝ`, `hv : SimplePolygon v`) show that it agrees with the
other standard descriptions.

| statement | Lean declaration | file |
|---|---|---|
| near every side the region is exactly one side of it | `region_orientedBoundary` (above); `region_orientedBoundary_of_turn`, `region_orientedBoundary_of_shoelace_pos`, `region_orientedBoundary_of_shoelace_neg` decide which case holds | `Region.lean`, `Orientation.lean` |
| topology | `frontier_region v hv : frontier (region v) = boundary v`, `isCompact_region`, `boundary_subset_region`, `interior_region v hv : interior (region v) = region v \ boundary v`, `closure_inner v hv : closure (region v \ boundary v) = region v` | `Frontier.lean`, `Jordan.lean` |
| the winding number off the curve takes the values `0` and `ε`, both attained, `ε = ±1` | `windingNumber_values` | `Jordan.lean` |
| polygonal Jordan curve theorem | `jordan v hv : (boundary v)ᶜ = (region v \ boundary v) ∪ (region v)ᶜ ∧ Disjoint (region v \ boundary v) (region v)ᶜ ∧ IsConnected (region v \ boundary v) ∧ IsConnected (region v)ᶜ ∧ IsOpen (region v \ boundary v) ∧ IsOpen (region v)ᶜ ∧ Bornology.IsBounded (region v \ boundary v) ∧ ¬ Bornology.IsBounded (region v)ᶜ` | `Jordan.lean` |
| the connected components of the complement of the curve | `connectedComponentIn_of_ne_zero`, `connectedComponentIn_of_eq_zero`, `connectedComponentIn_cases` | `Jordan.lean` |
| region = curve ∪ points whose component of the complement is bounded | `region_eq_bounded`; over `ℂ`: `region_eq_polyInterior v hv : region v = boundary v ∪ toC ⁻¹' polyInterior (toC ∘ v)`, `toC_image_region`, `toC_image_boundary`, `preimage_polyInterior` | `Jordan.lean`, `PolyInterior.lean` |
| ray-crossing parity | `mem_region_iff_odd_crossings v hv (hx : x ∉ boundary v) (hd0 : d ≠ 0) (hd : ∀ k, ∀ s : ℝ, 0 ≤ s → x + s • d ≠ v k) : x ∈ region v ↔ Odd {k \| ∃ s : ℝ, 0 ≤ s ∧ x + s • d ∈ side v k}.ncard`; `ray_side_unique` (such a ray meets each side at most once), `exists_generic_ray` (such rays exist) | `Parity.lean` |
| shoelace formula and orientation | `volume_region v hv : volume (region v) = ENNReal.ofReal (\|shoelace v\| / 2)`, `shoelace_ne_zero`, `shoelace_pos_iff v hv : 0 < shoelace v ↔ ∀ x, x ∉ boundary v → windingNumber v x = 0 ∨ windingNumber v x = 1`, `shoelace_neg_iff` | `Orientation.lean` |
| convex polygons, the unit square | `region_eq_convexHull v (hconv : ∀ k j, j ≠ k → j ≠ k + 1 → 0 < cross (v k) (v (k + 1)) (v j)) : region v = convexHull ℝ (range v)`, `simplePolygon_of_convex`, `region_subset_convexHull`; `region_unitSquare : region unitSquare = Icc (0 : ℝ × ℝ) 1`, `simplePolygon_unitSquare`, `shoelace_unitSquare` | `Convex.lean`, `Orientation.lean` |

## Differences between the formalisation and the paper

1. **Polygons.**  A polygon is a simple closed polygon given by the list of its vertices (at
   least three, pairwise distinct; collinear consecutive sides are allowed).  Polygons with holes
   or with several components are covered only through the hypothesis `OrientedBoundary`
   (`main_theorem_of_orientedBoundary`, `stein_conjecture_of_orientedBoundary`); there is no
   vertex-list theorem for them.
2. **The region** is defined by the winding number and proved equal to the other descriptions
   (previous section).  Limitations of those results: the ray-parity criterion
   `mem_region_iff_odd_crossings` is proved only for rays that pass through no vertex (there is no
   convention for rays through vertices); "the complement of the curve has exactly two
   components" is stated through `connectedComponentIn` (`jordan`, `connectedComponentIn_cases`),
   not as a statement on the cardinality of `ConnectedComponents`; `region_eq_convexHull` is for
   strictly convex counter-clockwise polygons.
3. **Lemma 2.1** is proved for every field of characteristic `0` from Mathlib's existence theorem
   for valuation subrings (`Ideal.image_subset_nonunits_valuationSubring`, which uses Zorn's
   lemma).  The paper's Zorn-free construction for countable fields is not formalised.
4. **Lemma 4.1 (Balance)** has the paper's statement but a different proof.  The paper cuts the
   sides into elementary pieces; the formal proof compares, for a line `L` parallel to `d`, the
   jumps across `L` of the indicator functions of the triangles and of `S` at generic points of
   `L`, and integrates along `L`.
5. **Main Theorem.**  `K` is a `Subfield ℝ` that has to contain the coordinates of the vertices of
   the triangles only (`IsTriangleOver K`); the doubled areas are given as elements `a i, a₀ : K`
   whose real values are prescribed; the minimum over `i` is replaced by an arbitrary bound `γ`
   (equivalent); no orientation hypothesis on `P` is needed.
6. **Valuations** are Mathlib's multiplicative valuations (table above).
7. **Stein's conjecture** is deduced from the Main Theorem with `K = ℝ` (and Lemma 2.1 for `ℝ`),
   not with the field generated by the coordinates.
8. **Not formalised:** the examples and remarks of §5–§6 and the complements of §7 (the
   residue-field statement, trapezoids).

## Files

| file | content |
|---|---|
| `Stein/Basic.lean` | `det`, `par`, `cross`, `OrientedBoundary` |
| `Stein/Algebra/Valuation.lean` | Lemma 2.1 |
| `Stein/Algebra/Sequences.lean` | §3: brackets, moves, side sequences, families |
| `Stein/Algebra/TheoremM.lean` | Lemma T, Theorem M |
| `Stein/Geometry/Triangle.lean` | triangles by inequalities, convex hull, area of a triangle, additivity of area |
| `Stein/Geometry/Balance.lean` | Lemma 4.1 |
| `Stein/Geometry/Dissection.lean` | `IsTriangle`, `IsDissection`, `Special`; Main Theorem and Stein's conjecture for sets with `OrientedBoundary` |
| `Stein/Geometry/Square.lean` | the unit square lies on the left of its boundary and is special |
| `Stein/Polygon/Winding.lean` | winding number of a closed polygonal curve; its behaviour near the sides of a simple one |
| `Stein/Polygon/Region.lean` | `SimplePolygon`, `windingNumber`, `region`; `region_orientedBoundary` |
| `Stein/Polygon/Frontier.lean` | frontier and compactness of the region |
| `Stein/Polygon/Rays.lean` | rays from a point off the curve; the winding number takes two values |
| `Stein/Polygon/Components.lean` | connectedness of the two sides of the curve |
| `Stein/Polygon/Jordan.lean` | polygonal Jordan curve theorem, components, closure and interior |
| `Stein/Polygon/PolyInterior.lean` | the description by bounded components, over `ℂ` |
| `Stein/Polygon/Parity.lean` | ray-crossing parity |
| `Stein/Polygon/Convex.lean` | convex polygons, the unit square |
| `Stein/Polygon/Orientation.lean` | shoelace formula, orientation |
| `Stein/Main.lean` | `SpecialPolygon`; `main_theorem`, `stein_conjecture`, `monsky` |
| `Stein/Axioms.lean` | `#print axioms` for the headline declarations |
