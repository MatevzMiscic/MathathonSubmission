"""Control runs: the procedure of Theorem M with ONE hypothesis removed.
  A  u is NOT a longest entry (whenever a non-longest entry with a unit partner exists)
  B  the partner u' = t u has v(t) > 0 (whenever such a partner of the longest entry exists)
  C  the polygon is NOT special (trapezoids, triangles, convex quadrilaterals)
  D  Lemma T without the hypothesis 'u is at least as long as w, w''
Usage: python3 run_controls.py N [seed]"""
import sys, random, collections
from merge import *
from dissect import *

def control(V, K, N, seed, label, gen, **kw):
    rng = random.Random(seed); out = collections.Counter(); first = None
    for n in range(N):
        name, edges, tris = gen(K, rng)
        tris = refine(tris, K, rng, rng.randint(2, 10))
        F = [side_seq(*t) for t in tris]
        nu = min(V.val(twice_area(t)) for t in tris)
        out["instances"] += 1
        out["instances where the inequality v(S) >= v(2)+nu itself fails"] += V.val(S(F)) < V.two + nu
        try:
            r = merge(V, F, nu=nu, **kw)
            out["run completed, all invariants kept" + (" (no deviation was possible)" if r["deviations"] == 0 and kw.get("require_balance", True) else "")] += 1
        except StepFailure as e:
            out["run stopped: " + e.kind] += 1
            if first is None and len(tris) <= 6: first = (e.kind, e.info, tris)
    print("-- control %s (%s, coordinates in %s, seed %d)" % (label, V.name, K.name, seed))
    for k, v in sorted(out.items()): print("     %-75s %d" % (k, v))
    if first: print("     a small instance:", first[0], first[1], "triangles", first[2])

def lemma_T(N, seed):
    rng = random.Random(seed); V = VQ(2); K = FieldQ(); c = collections.Counter()
    def vec(): return (K.small(rng), K.small(rng))
    for _ in range(N):
        u, w, w2 = vec(), vec(), vec()
        if vzero(u): continue
        hyp = vval(V, u) <= vval(V, w) and vval(V, u) <= vval(V, w2)
        ok = V.val(det(w, w2)) >= min(V.val(det(u, w)), V.val(det(u, w2)))
        c[("hypothesis holds" if hyp else "hypothesis fails") + ", conclusion " + ("holds" if ok else "FAILS")] += 1
    print("-- control D: Lemma T on %d random triples (v_2 on Q)" % N)
    for k, v in sorted(c.items()): print("     %-75s %d" % (k, v))
    assert c["hypothesis holds, conclusion FAILS"] == 0

if __name__ == "__main__":
    N = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    sp = lambda K, rng: random_special(K, rng)
    control(VQ(2), FieldQ(), N, seed, "A: non-longest entry", sp, choose="nonlongest")
    control(VQ(2), FieldQ(), N, seed + 1, "B: partner with v(t) > 0", sp, partner="nonunit")
    control(VQ(2), FieldQ(), N, seed + 2, "C: non-special polygon", random_nonspecial, require_balance=False)
    control(VSqrt5(), FieldQuad(5), N // 4, seed + 3, "A: non-longest entry", sp, choose="nonlongest")
    control(VSqrt5(), FieldQuad(5), N // 4, seed + 4, "B: partner with v(t) > 0", sp, partner="nonunit")
    control(VSqrt5(), FieldQuad(5), N // 4, seed + 5, "C: non-special polygon", random_nonspecial, require_balance=False)
    lemma_T(20 * N, seed + 6)
    print("CONTROL RUNS DONE")
