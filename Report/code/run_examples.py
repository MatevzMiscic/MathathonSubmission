"""The worked examples of the report, recomputed exactly.
Usage: python3 run_examples.py   (prints a log)"""
from fractions import Fraction as Fr
from merge import *
from dissect import twice_area, balance_identity, convex, is_special

def show(c): return "(" + ", ".join("(%s,%s)" % w for w in c) + ")"

print("== Example: Lemma T needs 'u longest' (v = v_2)")
V = VQ(2); u, w, w2 = (2, 0), (1, 1), (0, 1)
print("  v(det(u,w)) =", V.val(det(u, w)), " v(det(u,w')) =", V.val(det(u, w2)),
      " v(det(w,w')) =", V.val(det(w, w2)))
assert (V.val(det(u, w)), V.val(det(u, w2)), V.val(det(w, w2))) == (1, 1, 0)

print("== Example: the unit square cut by a diagonal, v = v_2")
t1 = side_seq((0, 0), (1, 0), (1, 1)); t2 = side_seq((0, 0), (1, 1), (0, 1))
# the report writes t2 starting at (1,1): rotate it
t2 = [(1, 1), (-1, 0), (0, -1)]
F = [t1, t2]
assert t1 == [(1, 0), (0, 1), (-1, -1)]
print("  t1 =", show(t1), " t2 =", show(t2), " S =", S(F))
J = t1 + t2
print("  join:", show(J), " bracket", bracket(J))
B = J[1:4]; q = J[4]
moved = [J[0], q] + B + [J[5]]
print("  swap: move u'=%s left past the block %s (sum %s):" % (q, show(B), sigma(B)))
print("        new sequence", show(moved), " bracket", bracket(moved),
      " change", bracket(moved) - bracket(J), " = -2 det(sum of block, u') =", -2 * det(sigma(B), q))
assert bracket(J) == 2 and bracket(moved) == 0 and bracket(moved) - bracket(J) == -2
A = [vadd(moved[0], moved[1])] + moved[2:]
print("  add: ", show(A), " bracket", bracket(A))
tr = []
st = merge(V, F, trace=tr)
print("  full procedure:", st)
assert st["S"] == 2 and st["cost"] == 2 and st["nu"] == 0 and st["bound_ok"] and V.val(st["S"]) == 1

print("== Example: T-junction.  Square [0,4]^2, diagonal (0,0)-(4,4), segment (4,0)-M, M=(2,2); v = v_2")
Bt = ((0, 0), (4, 4), (0, 4)); A1 = ((0, 0), (4, 0), (2, 2)); A2 = ((4, 0), (4, 4), (2, 2))
tris = [Bt, A1, A2]
edges, _ = convex([(0, 0), (4, 0), (4, 4), (0, 4)])
assert balance_identity(tris, edges) and is_special(edges)
F = [side_seq(*t) for t in tris]
for nm, t, c in zip(("B", "A1", "A2"), tris, F): print("  %-2s" % nm, show(c), " 2*area =", twice_area(t))
tr = []
st = merge(V, F, trace=tr)
for kind, fam, s in tr:
    print("   %-4s S=%-3s " % (kind, s), " ; ".join(show(c) for c in fam))
print("  result:", st, " v(S) =", V.val(st["S"]), ">= v(2)+nu =", 1 + st["nu"])
assert st["S"] == 32 and st["bound_ok"] and st["joins"] >= 1

print("== Example: the fan in Q(sqrt5); cone the unit square from (phi-1, 1/3)")
phi = QF(Fr(1, 2), Fr(1, 2), 5); V5 = VSqrt5()
assert phi * phi == phi + 1 and (phi - 1) * phi == 1 and (2 - phi) * phi * phi == 1
a = (phi - 1, QF(Fr(1, 3), 0, 5))
sq = [(0, 0), (1, 0), (1, 1), (0, 1)]
tris = [(sq[i], sq[(i + 1) % 4], a) for i in range(4)]
d = [twice_area(t) for t in tris]
names = ["bottom", "right", "top", "left"]
for nm, x in zip(names, d): print("  %-6s 2*area = %-22s v = %s" % (nm, x, V5.val(x)))
assert d[0] == Fr(1, 3) and d[1] == 2 - phi and d[2] == Fr(2, 3) and d[3] == phi - 1
assert [V5.val(x) for x in d] == [0, 0, 1, 0]
c = d[0]
res = [V5.residue(fdiv(x, c)) for x in d if V5.val(x) == 0]
print("  residues of (2 area)/c, c = 1/3, in F_4 as (x mod 2, y mod 2) for x + y*phi:", res)
assert res == [(1, 0), (0, 1), (1, 1)]         # 1, phi^2 = 1 + phi ... see below
assert V5.residue(phi) == (0, 1) and V5.residue(phi * phi) == (1, 1)
tot = (sum(r[0] for r in res) % 2, sum(r[1] for r in res) % 2)
print("  number of triangles of minimal valuation:", len(res), " sum of residues:", tot)
assert tot == (0, 0) and len(res) == 3
F = [side_seq(*t) for t in tris]
st = merge(V5, F)
print("  merging procedure:", st, " v(S) =", V5.val(st["S"]))
assert st["S"] == 2 and st["bound_ok"]

print("== Example: the trapezoid (0,0),(2,0),(1,1),(0,1) (not special), 3 triangles of area 1/2")
tris = [((0, 0), (1, 0), (0, 1)), ((1, 0), (1, 1), (0, 1)), ((1, 0), (2, 0), (1, 1))]
edges, _ = convex([(0, 0), (2, 0), (1, 1), (0, 1)])
assert all(twice_area(t) == 1 for t in tris) and balance_identity(tris, edges) and not is_special(edges)
F = [side_seq(*t) for t in tris]
print("  S =", S(F), " v_2(S) =", V.val(S(F)), " < v(2)+nu = 1 ; family balanced:", is_balanced(F))
try:
    merge(V, F); raise SystemExit("unexpected")
except StepFailure as e:
    print("  merging procedure stops with:", e.kind)
print("== The valuations on Q(sqrt5), Q(sqrt2): axioms (V2), (V3) on random elements")
import random
rng = random.Random(5)
for Vx, dd in ((VSqrt5(), 5), (VSqrt2(), 2)):
    n = 0
    for _ in range(5000):
        x = QF(Fr(rng.randint(-40, 40), rng.randint(1, 16)), Fr(rng.randint(-40, 40), rng.randint(1, 16)), dd)
        y = QF(Fr(rng.randint(-40, 40), rng.randint(1, 16)), Fr(rng.randint(-40, 40), rng.randint(1, 16)), dd)
        if x == 0 or y == 0: continue
        assert Vx.val(x * y) == Vx.val(x) + Vx.val(y)
        assert Vx.val(x + y) >= min(Vx.val(x), Vx.val(y))
        assert Vx.val(x / y) == Vx.val(x) - Vx.val(y)
        n += 1
    assert Vx.val(QF(2, 0, dd)) == Vx.two
    print("  %s: %d random pairs OK" % (Vx.name, n))
print("ALL EXAMPLES OK")
