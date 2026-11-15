"""Exact-arithmetic implementation of the merging procedure of Theorem M
(join / swap / add) and of the objects around it.

Fields:      Q (fractions.Fraction) and Q(sqrt d) (class QF, exact).
Valuations:  VQ(p)      p-adic valuation on Q
             VSqrt5()   the valuation of Q(sqrt 5) at the inert prime 2 (residue field F_4)
             VSqrt2()   the valuation of Q(sqrt 2) at the ramified prime sqrt 2,
                        normalised so that v(sqrt 2) = 1, v(2) = 2
A valuation object has  .val(x) (math.inf for 0)  and  .two = val(2).
Vectors are pairs; a sequence is a list of vectors; a family is a list of sequences.
"""
from fractions import Fraction
import math

INF = math.inf


# ---------------------------------------------------------------- fields
class QF:
    """a + b*sqrt(d), a, b rational, d a fixed squarefree integer > 1"""
    __slots__ = ("a", "b", "d")

    def __init__(self, a, b, d):
        self.a = Fraction(a); self.b = Fraction(b); self.d = d

    def _c(self, o):
        if isinstance(o, QF):
            assert o.d == self.d
            return o
        return QF(o, 0, self.d)

    def __add__(self, o): o = self._c(o); return QF(self.a + o.a, self.b + o.b, self.d)
    __radd__ = __add__
    def __neg__(self): return QF(-self.a, -self.b, self.d)
    def __sub__(self, o): o = self._c(o); return QF(self.a - o.a, self.b - o.b, self.d)
    def __rsub__(self, o): return self._c(o) - self
    def __mul__(self, o):
        o = self._c(o)
        return QF(self.a * o.a + self.d * self.b * o.b, self.a * o.b + self.b * o.a, self.d)
    __rmul__ = __mul__
    def inv(self):
        n = self.a * self.a - self.d * self.b * self.b
        return QF(self.a / n, -self.b / n, self.d)
    def __truediv__(self, o): return self * self._c(o).inv()
    def __rtruediv__(self, o): return self._c(o) * self.inv()
    def __eq__(self, o):
        if isinstance(o, (int, Fraction)): return self.b == 0 and self.a == o
        return isinstance(o, QF) and self.a == o.a and self.b == o.b
    def __hash__(self): return hash((self.a, self.b))
    def sign(self):
        """exact sign of the real number a + b sqrt d"""
        a, b, d = self.a, self.b, self.d
        if b == 0: return (a > 0) - (a < 0)
        if a == 0: return (b > 0) - (b < 0)
        if a > 0 and b > 0: return 1
        if a < 0 and b < 0: return -1
        s = (a * a > d * b * b) - (a * a < d * b * b)   # sign of |a| - |b| sqrt d
        return s if a > 0 else -s
    def __repr__(self):
        if self.b == 0: return str(self.a)
        return "(%s %s %s*sqrt%d)" % (self.a, "+" if self.b > 0 else "-", abs(self.b), self.d)


def sign(x):
    return x.sign() if isinstance(x, QF) else (x > 0) - (x < 0)


def is_zero(x):
    return x == 0


# ---------------------------------------------------------------- valuations
def vp_int(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


def vp(x, p):
    x = Fraction(x)
    if x == 0: return INF
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


class VQ:
    def __init__(self, p): self.p = p; self.two = vp(2, p); self.name = "v_%d on Q" % p
    def val(self, x): return vp(x, self.p)


class VSqrt5:
    """2 is inert in Q(sqrt5).  a + b sqrt5 = (a - b) + 2b*phi, phi = (1+sqrt5)/2, and
    v(x + y phi) = min(v_2(x), v_2(y))  (the norm x^2 + xy - y^2 is odd unless x, y both even)."""
    two = 1; name = "v at the inert prime 2 of Q(sqrt5)"
    def val(self, x):
        if not isinstance(x, QF): return vp(x, 2)
        return min(vp(x.a - x.b, 2), vp(2 * x.b, 2))
    def residue(self, x):
        """image in F_4 = {0,1,phi,phi^2} of an element with val >= 0, as a pair (x mod 2, y mod 2)"""
        if not isinstance(x, QF): x = QF(x, 0, 5)
        assert self.val(x) >= 0
        r = []
        for c in (x.a - x.b, 2 * x.b):
            c = Fraction(c)
            r.append((c.numerator * pow(c.denominator, -1, 2)) % 2)
        return tuple(r)


class VSqrt2:
    """sqrt2 is a uniformiser of Q(sqrt2) above 2: v(a + b sqrt2) = min(2 v_2(a), 2 v_2(b) + 1)."""
    two = 2; name = "v at the ramified prime sqrt2 of Q(sqrt2), v(2) = 2"
    def val(self, x):
        if not isinstance(x, QF): return 2 * vp(x, 2)
        return min(2 * vp(x.a, 2), 2 * vp(x.b, 2) + 1)


# ---------------------------------------------------------------- vectors, sequences
def det(a, b): return a[0] * b[1] - a[1] * b[0]
def vadd(a, b): return (a[0] + b[0], a[1] + b[1])
def vsub(a, b): return (a[0] - b[0], a[1] - b[1])
def vzero(a): return is_zero(a[0]) and is_zero(a[1])
def vval(V, w): return min(V.val(w[0]), V.val(w[1]))


def sigma(c):
    s = (0, 0)
    for w in c: s = vadd(s, w)
    return s


def bracket(c):
    """[c] = sum_{i<j} det(c_i, c_j), computed with partial sums"""
    tot = 0; s = (0, 0)
    for w in c:
        tot = tot + det(s, w); s = vadd(s, w)
    return tot


def S(F):
    tot = 0
    for c in F: tot = tot + bracket(c)
    return tot


def is_closed(F): return all(vzero(sigma(c)) for c in F)


def flat_defect(V, nu, c):
    """None if v(det(w,w')) >= nu for all entries w, w' of c; otherwise a violating pair"""
    for i in range(len(c)):
        for j in range(i + 1, len(c)):
            if V.val(det(c[i], c[j])) < nu:
                return (c[i], c[j])
    return None


def is_flat(V, nu, F): return all(flat_defect(V, nu, c) is None for c in F)


def direction_sums(vectors):
    """group non-zero vectors by direction (line through 0); return list of (representative, sum)"""
    classes = []
    for w in vectors:
        if vzero(w): continue
        for cl in classes:
            if is_zero(det(cl[0], w)):
                cl[1] = vadd(cl[1], w); break
        else:
            classes.append([w, w])
    return classes


def is_balanced(F):
    return all(vzero(s) for _, s in direction_sums([w for c in F for w in c]))


def side_seq(p, q, r): return [vsub(q, p), vsub(r, q), vsub(p, r)]


# ---------------------------------------------------------------- the merging procedure
class StepFailure(Exception):
    def __init__(self, kind, info=None):
        Exception.__init__(self, kind); self.kind = kind; self.info = info


def fdiv(a, b):
    """exact a / b (Python ints are converted to Fractions first)"""
    if isinstance(a, int): a = Fraction(a)
    if isinstance(b, int): b = Fraction(b)
    return a / b


def ratio(u, w):
    """t with w = t*u, for w parallel to u != 0"""
    return fdiv(w[0], u[0]) if not is_zero(u[0]) else fdiv(w[1], u[1])


def merge(V, F, nu=None, choose="longest", partner="unit", trace=None, check=True,
          require_balance=True):
    """Run the procedure of the proof of Theorem M on the family F for the valuation V.

    choose  = "longest"     : u is an entry of minimal valuation (the proof)
            = "nonlongest"  : CONTROL - u is an entry of non-minimal valuation, when one with
                              a parallel partner exists
    partner = "unit"        : u' = t u at another position with v(t) = 0 (the proof)
            = "nonunit"     : CONTROL - a parallel partner with v(t) > 0, when one exists
    With check=True every invariant used in the proof is asserted after every move:
    closedness, nu-flatness, balance, the exact change of S, and that each change of S has
    valuation >= v(2) + nu.  A failed invariant raises StepFailure(kind).
    Returns a dict with the number of moves and the total swap cost (which must equal S(F)).
    """
    F = [list(c) for c in F]
    if nu is None:
        nu = min([V.val(det(c[i], c[j])) for c in F for i in range(len(c))
                  for j in range(i + 1, len(c))] + [INF])
    bound = V.two + nu
    S0 = S(F)
    if check:
        if not is_closed(F): raise StepFailure("input not closed")
        if not is_flat(V, nu, F): raise StepFailure("input not flat")
    if require_balance and not is_balanced(F): raise StepFailure("input not balanced")
    stats = dict(joins=0, swaps=0, adds=0, deviations=0, cost=0, nu=nu)
    while True:
        F = [[w for w in c if not vzero(w)] for c in F]
        F = [c for c in F if c]
        if not F: break
        pos = [(i, j) for i, c in enumerate(F) for j in range(len(c))]
        vals = {ij: vval(V, F[ij[0]][ij[1]]) for ij in pos}
        vmin = min(vals.values())

        def partners(ij, unit):
            u = F[ij[0]][ij[1]]; out = []
            for kl in pos:
                if kl == ij: continue
                w = F[kl[0]][kl[1]]
                if is_zero(det(u, w)):
                    vt = V.val(ratio(u, w))
                    if (vt == 0) == unit and (unit or vt > 0): out.append(kl)
            return out

        # ---- Step 1
        cand = [ij for ij in pos if vals[ij] == vmin]
        ij = cand[0]; deviated = False
        if choose == "nonlongest":
            alt = [x for x in pos if vals[x] > vmin and partners(x, True)]
            if alt:
                ij = max(alt, key=lambda x: vals[x]); deviated = True
        want_unit = True
        if partner == "nonunit" and not deviated and partners(ij, False):
            want_unit = False; deviated = True
        ps = partners(ij, want_unit)
        if not ps:
            raise StepFailure("no partner", F[ij[0]][ij[1]])
        kl = ps[0]
        if deviated: stats["deviations"] += 1
        u = F[ij[0]][ij[1]]; u2 = F[kl[0]][kl[1]]
        # ---- Step 2: join
        if ij[0] != kl[0]:
            x, y = F[ij[0]], F[kl[0]]
            before = S(F)
            new = x + y
            F = [c for n, c in enumerate(F) if n not in (ij[0], kl[0])] + [new]
            a, b = ij[1], len(x) + kl[1]
            stats["joins"] += 1
            if S(F) != before: raise StepFailure("join changed S")
            d = flat_defect(V, nu, new)
            if d is not None: raise StepFailure("flatness lost in join", d)
            if trace is not None: trace.append(("join", [list(c) for c in F], S(F)))
        else:
            a, b = sorted((ij[1], kl[1]))
        c = F[-1] if ij[0] != kl[0] else F[ij[0]]
        idx = len(F) - 1 if ij[0] != kl[0] else ij[0]
        # ---- Step 3: swaps (move the later entry to the left until adjacent)
        while b > a + 1:
            p, q = c[b - 1], c[b]
            old = bracket(c)
            c[b - 1], c[b] = q, p
            change = bracket(c) - old
            if change != -2 * det(p, q): raise StepFailure("swap formula")
            if check and V.val(change) < bound: raise StepFailure("swap cost too small", (p, q))
            stats["cost"] = stats["cost"] - change
            stats["swaps"] += 1
            b -= 1
        if trace is not None: trace.append(("swap", [list(s) for s in F], S(F)))
        # ---- Step 4: add
        old = bracket(c)
        p, q = c[a], c[b]
        c[a:b + 1] = [vadd(p, q)]
        if bracket(c) != old: raise StepFailure("add changed bracket")
        stats["adds"] += 1
        if trace is not None: trace.append(("add", [list(s) for s in F], S(F)))
        if check:
            if not is_closed(F): raise StepFailure("closedness lost")
            d = flat_defect(V, nu, F[idx])
            if d is not None: raise StepFailure("flatness lost", d)
            if require_balance and not is_balanced(F): raise StepFailure("balance lost")
    if stats["cost"] != S0: raise StepFailure("total swap cost differs from S")
    stats["S"] = S0
    stats["bound_ok"] = V.val(S0) >= bound
    return stats
