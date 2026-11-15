import Stein.Basic
import Stein.Algebra.Valuation
import Stein.Algebra.Sequences
import Stein.Algebra.TheoremM
import Stein.Geometry.Triangle
import Stein.Geometry.Balance
import Stein.Geometry.Dissection
import Stein.Geometry.Square
import Stein.Polygon.Winding
import Stein.Polygon.Region
import Stein.Polygon.Frontier
import Stein.Polygon.Rays
import Stein.Polygon.Components
import Stein.Polygon.Jordan
import Stein.Polygon.PolyInterior
import Stein.Polygon.Parity
import Stein.Polygon.Convex
import Stein.Polygon.Orientation
import Stein.Main
import Stein.Axioms

/-!
# Stein's conjecture and Monsky's theorem

A special polygon (for every direction, the side vectors parallel to it sum to zero) has no
dissection into an odd number of triangles of equal area; in particular (Monsky) the unit square
has none.

* `Stein/Basic.lean` : `det`, `par`, `cross`, `OrientedBoundary`.
* `Stein/Algebra/` : the valuation with `v 2 < 1` (Lemma 2.1), sequences of vectors and their
  brackets (§3), Lemma T and Theorem M (§5).
* `Stein/Geometry/` : area of triangles, the balance lemma (Lemma 4.1), dissections and the Main
  Theorem for sets lying on the left of their oriented boundary, the unit square.
* `Stein/Polygon/` : winding number of a closed polygon, the region bounded by a simple polygon,
  the polygonal Jordan curve theorem and the equivalent descriptions of the region.
* `Stein/Main.lean` : `Stein.main_theorem`, `Stein.stein_conjecture`, `Stein.monsky`.
* `Stein/Axioms.lean` : `#print axioms` for the headline declarations.
-/
