import Stein.Main
import Stein.Polygon.PolyInterior
import Stein.Polygon.Parity
import Stein.Polygon.Orientation

/-!
# Axiom audit

`#print axioms` for the headline declarations.  Expected output for each of them: a subset of
`[propext, Classical.choice, Quot.sound]`.
-/

/-! ### The proof of the Main Theorem, Stein's conjecture and Monsky's theorem -/

#print axioms Stein.exists_valuation_two_pos
#print axioms Stein.bracket_append
#print axioms Stein.bracket_join
#print axioms Stein.bracket_swap
#print axioms Stein.bracket_add
#print axioms Stein.bracket_sideSeq
#print axioms Stein.det_sideSeq
#print axioms Stein.lemma_T
#print axioms Stein.theorem_M
#print axioms Stein.volume_triangle
#print axioms Stein.IsDissection.volume_eq_sum
#print axioms Stein.balance
#print axioms Stein.balanced_of_special
#print axioms Stein.main_theorem_of_orientedBoundary
#print axioms Stein.stein_conjecture_of_orientedBoundary
#print axioms Stein.Polygon.region_orientedBoundary
#print axioms Stein.Polygon.frontier_region
#print axioms Stein.main_theorem
#print axioms Stein.stein_conjecture
#print axioms Stein.stein_conjecture_fin
#print axioms Stein.square_boundary
#print axioms Stein.main_theorem_square
#print axioms Stein.monsky
#print axioms Stein.monsky_fin

/-! ### The region bounded by a simple polygon: equivalent descriptions -/

#print axioms Stein.Polygon.windingNumber_values
#print axioms Stein.Polygon.jordan
#print axioms Stein.Polygon.isConnected_inner
#print axioms Stein.Polygon.isConnected_outer
#print axioms Stein.Polygon.connectedComponentIn_of_ne_zero
#print axioms Stein.Polygon.connectedComponentIn_of_eq_zero
#print axioms Stein.Polygon.closure_inner
#print axioms Stein.Polygon.interior_region
#print axioms Stein.Polygon.region_eq_bounded
#print axioms Stein.Polygon.toC_image_boundary
#print axioms Stein.Polygon.windingNumber_ne_zero_subset_polyInterior
#print axioms Stein.Polygon.polyInterior_subset_windingNumber_ne_zero
#print axioms Stein.Polygon.region_eq_polyInterior
#print axioms Stein.Polygon.toC_image_region
#print axioms Stein.Polygon.mem_region_iff_odd_crossings
#print axioms Stein.Polygon.ray_side_unique
#print axioms Stein.Polygon.exists_generic_ray
#print axioms Stein.Polygon.volume_region
#print axioms Stein.Polygon.shoelace_ne_zero
#print axioms Stein.Polygon.shoelace_pos_iff
#print axioms Stein.Polygon.shoelace_neg_iff
#print axioms Stein.Polygon.region_orientedBoundary_of_shoelace_pos
#print axioms Stein.Polygon.region_orientedBoundary_of_shoelace_neg
#print axioms Stein.Polygon.region_eq_convexHull
#print axioms Stein.Polygon.simplePolygon_of_convex
#print axioms Stein.Polygon.region_unitSquare
#print axioms Stein.Polygon.simplePolygon_unitSquare
