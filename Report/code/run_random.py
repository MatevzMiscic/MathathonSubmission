"""Random dissections of special polygons, with T-junctions: the merging procedure of Theorem M
with every invariant asserted, the balance lemma, and the Main Theorem inequality.
Usage: python3 run_random.py N_Q N_QUAD [seed]"""
import sys, random, time, collections
from merge import *
from dissect import *

def run(V, K, N, seed, maxsteps):
    rng = random.Random(seed); t0 = time.time()
    st = collections.Counter(); kinds = collections.Counter()
    for n in range(N):
        name, edges, tris = random_special(K, rng)
        tris = refine(tris, K, rng, rng.randint(2, maxsteps))
        kinds[name.split(" (")[0]] += 1
        st["instances"] += 1; st["triangles"] += len(tris)
        st["max triangles"] = max(st["max triangles"], len(tris))
        tj = count_t_junctions(tris); st["T-junction incidences"] += tj; st["instances with a T-junction"] += tj > 0
        assert all(sign(twice_area(t)) > 0 for t in tris)
        assert balance_identity(tris, edges), "balance lemma fails"
        F = [side_seq(*t) for t in tris]
        nu = min(V.val(twice_area(t)) for t in tris)
        r = merge(V, F, nu=nu)                       # raises StepFailure if any invariant fails
        assert r["bound_ok"] and r["S"] == sum(twice_area(t) for t in tris)
        st["joins"] += r["joins"]; st["swaps"] += r["swaps"]; st["adds"] += r["adds"]
        st["bound attained (v(S) = v(2)+nu)"] += V.val(r["S"]) == V.two + nu
        st["v(S) < v(p)+nu for the residue characteristic p (only informative if p != 2)"] += 0
        if isinstance(V, VQ) and V.p != 2:
            st["instances with v_p(S) < v_p(p) + nu (no factor p is gained)"] += V.val(r["S"]) < 1 + nu
        if isinstance(V, VSqrt5):
            mins = [twice_area(t) for t in tris if V.val(twice_area(t)) == nu]
            res = [V.residue(fdiv(x, mins[0])) for x in mins]
            assert (sum(a for a, b in res) % 2, sum(b for a, b in res) % 2) == (0, 0), "residue sum"
            st["instances with an ODD number of triangles of minimal valuation"] += len(mins) % 2
        else:
            mins = [t for t in tris if V.val(twice_area(t)) == nu]
            if V.two > 0 and isinstance(V, VQ):
                assert len(mins) % 2 == 0, "parity over F_2"
    del st["v(S) < v(p)+nu for the residue characteristic p (only informative if p != 2)"]
    print("-- %s, coordinates in %s, seed %d: all assertions passed (%.0f s)" % (V.name, K.name, seed, time.time() - t0))
    for k, v in st.items(): print("     %-70s %d" % (k, v))
    print("     polygons:", dict(kinds))

def fans(N, seed):
    """the unit square coned from a random interior point with coordinates in Q(sqrt5)"""
    rng = random.Random(seed); K = FieldQuad(5); V = VSqrt5(); odd = 0
    sq = [(0, 0), (1, 0), (1, 1), (0, 1)]
    for n in range(N):
        a = (K.unit_interval(rng), K.unit_interval(rng))
        tris = [(sq[i], sq[(i + 1) % 4], a) for i in range(4)]
        d = [twice_area(t) for t in tris]; nu = min(V.val(x) for x in d)
        mins = [x for x in d if V.val(x) == nu]
        res = [V.residue(fdiv(x, mins[0])) for x in mins]
        assert (sum(r[0] for r in res) % 2, sum(r[1] for r in res) % 2) == (0, 0)
        r = merge(V, [side_seq(*t) for t in tris], nu=nu)
        assert r["bound_ok"] and r["S"] == 2
        odd += len(mins) % 2
    print("-- %d fans of the unit square from random points of Q(sqrt5)^2 (seed %d): residue sum 0 in F_4 and"
          " merging procedure passed in all; ODD number of triangles of minimal valuation in %d" % (N, seed, odd))


if __name__ == "__main__":
    NQ = int(sys.argv[1]); NQD = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    run(VQ(2), FieldQ(), NQ, seed, 12)
    run(VQ(3), FieldQ(), NQ // 2, seed + 1, 12)
    run(VQ(5), FieldQ(), NQ // 2, seed + 2, 12)
    run(VSqrt5(), FieldQuad(5), NQD, seed + 3, 9)
    run(VSqrt2(), FieldQuad(2), NQD, seed + 4, 9)
    fans(NQD * 10, seed + 5)
    print("RANDOM RUNS OK")
