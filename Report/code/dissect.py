"""Random dissections (with T-junctions) of polygons, in exact arithmetic.

A polygon is given by a list of oriented boundary edges (a, b) (region on the left) and an
initial triangulation; refine() then repeatedly subdivides ONE triangle at a time, so that
T-junctions with the neighbouring triangles appear:
   star : a new vertex inside a triangle             (1 -> 3 triangles)
   side : a new vertex on a side of one triangle     (1 -> 2 triangles; T-junction or boundary node)
   cut  : new vertices on two sides of one triangle  (1 -> 3 triangles; two T-junctions)
"""
from fractions import Fraction
from merge import QF, det, vadd, vsub, vzero, sign, direction_sums, is_zero

DENS = [2, 3, 4, 5, 6, 7, 8, 12, 16]


class FieldQ:
    name = "Q"
    def small(self, rng):          # a random element (not nec. positive)
        return Fraction(rng.randint(-9, 9), rng.choice([1, 1, 2, 3, 4, 8]))
    def unit_interval(self, rng):  # a random element of (0,1)
        d = rng.choice(DENS); return Fraction(rng.randint(1, d - 1), d)
    def positive(self, rng):
        return Fraction(rng.randint(1, 7), rng.choice([1, 1, 2, 3, 4]))


class FieldQuad:
    def __init__(self, d): self.d = d; self.name = "Q(sqrt%d)" % d
    def small(self, rng):
        return QF(Fraction(rng.randint(-6, 6), rng.choice([1, 1, 2, 3, 4])),
                  Fraction(rng.randint(-4, 4), rng.choice([1, 1, 2, 3, 4])), self.d)
    def unit_interval(self, rng):
        while True:
            x = QF(Fraction(rng.randint(-8, 8), rng.choice(DENS)),
                   Fraction(rng.randint(-4, 4), rng.choice(DENS)), self.d)
            if sign(x) > 0 and sign(1 - x) > 0: return x
    def positive(self, rng):
        while True:
            x = self.small(rng)
            if sign(x) > 0: return x


def comb(p, q, t):  # p + t (q - p)
    return (p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1]))


def refine(tris, K, rng, steps):
    tris = list(tris)
    for _ in range(steps):
        i = rng.randrange(len(tris))
        p, q, r = tris.pop(i)
        k = rng.randrange(3)
        p, q, r = (p, q, r)[k:] + (p, q, r)[:k]
        kind = rng.choice(["star", "side", "side", "cut"])
        if kind == "star":
            a, b, c = K.positive(rng), K.positive(rng), K.positive(rng)
            s = a + b + c
            m = ((a * p[0] + b * q[0] + c * r[0]) / s, (a * p[1] + b * q[1] + c * r[1]) / s)
            tris += [(p, q, m), (q, r, m), (r, p, m)]
        elif kind == "side":
            m = comb(p, q, K.unit_interval(rng))
            tris += [(p, m, r), (m, q, r)]
        else:
            m = comb(p, q, K.unit_interval(rng)); n = comb(p, r, K.unit_interval(rng))
            tris += [(p, m, n), (m, q, r), (m, r, n)]
    return tris


def twice_area(t): return det(vsub(t[1], t[0]), vsub(t[2], t[0]))


def count_t_junctions(tris):
    """number of pairs (vertex x, triangle side s) with x in the relative interior of s"""
    pts = set(v for t in tris for v in t); n = 0
    for t in tris:
        for a, b in ((t[0], t[1]), (t[1], t[2]), (t[2], t[0])):
            ab = vsub(b, a)
            for x in pts:
                if x == a or x == b: continue
                ax = vsub(x, a)
                if is_zero(det(ab, ax)):
                    dot = ab[0] * ax[0] + ab[1] * ax[1]
                    if sign(dot) > 0 and sign(ab[0] * ab[0] + ab[1] * ab[1] - dot) > 0: n += 1
    return n


def balance_identity(tris, edges):
    """Lemma (Balance), checked directly: for every direction, the triangle side vectors in that
    direction and the polygon edge vectors in that direction have the same sum."""
    vs = [vsub(b, a) for t in tris for a, b in ((t[0], t[1]), (t[1], t[2]), (t[2], t[0]))]
    vs += [vsub(a, b) for a, b in edges]            # minus the edge vectors
    return all(vzero(s) for _, s in direction_sums(vs))


def is_special(edges):
    return all(vzero(s) for _, s in direction_sums([vsub(b, a) for a, b in edges]))


# ------------------------------------------------------------------ polygons
def convex(vertices):
    """convex polygon, counter-clockwise vertices: edges and the fan triangulation"""
    n = len(vertices)
    edges = [(vertices[i], vertices[(i + 1) % n]) for i in range(n)]
    tris = [(vertices[0], vertices[i], vertices[i + 1]) for i in range(1, n - 1)]
    for t in tris: assert sign(twice_area(t)) > 0
    return edges, tris


def random_matrix(K, rng):
    while True:
        a, b, c, d = (K.small(rng) for _ in range(4))
        if sign(a * d - b * c) > 0: return (a, b, c, d)


def apply(M, p):
    a, b, c, d = M
    return (a * p[0] + b * p[1], c * p[0] + d * p[1])


def parallelogram(K, rng):
    M = random_matrix(K, rng)
    return convex([apply(M, p) for p in ((0, 0), (1, 0), (1, 1), (0, 1))])


def zonogon(K, rng, k):
    """centrally symmetric convex 2k-gon with random generators"""
    while True:
        gens = []
        for _ in range(k):
            g = (K.small(rng), K.positive(rng))        # upper half plane
            gens.append(g)
        if all(not is_zero(det(gens[i], gens[j])) for i in range(k) for j in range(i)): break
    # sort by angle (all in the open upper half plane): g before h iff det(g, h) > 0
    import functools
    gens.sort(key=functools.cmp_to_key(lambda g, h: -sign(det(g, h))))
    vs = [(0, 0)]
    for g in gens + [(-g[0], -g[1]) for g in gens]:
        vs.append(vadd(vs[-1], g))
    assert vzero(vs[-1])
    return convex(vs[:-1])


POLYOMINOES = {
    "L-tromino": [(0, 0), (1, 0), (0, 1)],
    "L-tetromino": [(0, 0), (1, 0), (2, 0), (0, 1)],
    "T-tetromino": [(0, 0), (1, 0), (2, 0), (1, 1)],
    "S-tetromino": [(0, 0), (1, 0), (1, 1), (2, 1)],
    "P-pentomino": [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2)],
    "plus-pentomino": [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)],
    "U-pentomino": [(0, 0), (1, 0), (2, 0), (0, 1), (2, 1)],
}


def polyomino(cells, M):
    """affine image of a polyomino: boundary edges (unit cell edges not shared by two cells)
    and the triangulation cutting every cell by a diagonal"""
    cells = set(cells); edges = []; tris = []
    for (i, j) in cells:
        c = [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)]
        nb = [(i, j - 1), (i + 1, j), (i, j + 1), (i - 1, j)]
        for k in range(4):
            if nb[k] not in cells: edges.append((apply(M, c[k]), apply(M, c[(k + 1) % 4])))
        mc = [apply(M, p) for p in c]
        tris += [(mc[0], mc[1], mc[2]), (mc[0], mc[2], mc[3])]
    return edges, tris


def random_special(K, rng):
    """returns (name, edges, initial triangulation) of a random special polygon"""
    kind = rng.choice(["square", "parallelogram", "zonogon3", "zonogon4", "polyomino", "polyomino"])
    I = (1, 0, 0, 1)
    if kind == "square": name, (e, t) = "unit square", convex([(0, 0), (1, 0), (1, 1), (0, 1)])
    elif kind == "parallelogram": name, (e, t) = "parallelogram", parallelogram(K, rng)
    elif kind == "zonogon3": name, (e, t) = "centrally symmetric hexagon", zonogon(K, rng, 3)
    elif kind == "zonogon4": name, (e, t) = "centrally symmetric octagon", zonogon(K, rng, 4)
    else:
        nm = rng.choice(sorted(POLYOMINOES))
        aff = rng.random() < 0.5
        M = random_matrix(K, rng) if aff else I
        name, (e, t) = nm + (" (affine image)" if aff else ""), polyomino(POLYOMINOES[nm], M)
    assert is_special(e)
    return name, e, t


def random_nonspecial(K, rng):
    kind = rng.choice(["trapezoid", "triangle", "quadrilateral"])
    while True:
        if kind == "trapezoid":
            p, q = rng.randint(1, 5), rng.randint(1, 5)
            vs = [(0, 0), (q, 0), (p, 1), (0, 1)]
        elif kind == "triangle":
            M = random_matrix(K, rng); vs = [apply(M, x) for x in ((0, 0), (1, 0), (0, 1))]
        else:
            M = random_matrix(K, rng); s, t = K.positive(rng), K.positive(rng)
            vs = [apply(M, x) for x in ((0, 0), (1, 0), (s, t), (0, 1))]
            if not (sign(s + t - 1) > 0): continue           # convex
        e, t = convex(vs)
        if not is_special(e): return kind, e, t
