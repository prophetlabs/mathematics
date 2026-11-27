"""
Independent check of Conjecture 4.1 for a given n by SAT:
count all families of 2^n lattice paths (0,0)->(n,n) with pairwise even
edge-intersections, and compare with the noncrossing-matching families F_M.
usage: python3 sat_count.py n
"""
import sys, itertools, time
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
from lp import paths, edges, noncrossing_matchings, F_M

n = int(sys.argv[1])
P = paths(n)
idx = {w: i + 1 for i, w in enumerate(P)}
E = {w: edges(w) for w in P}
cnf = CNF()
nodd = 0
for a, b in itertools.combinations(P, 2):
    if len(E[a] & E[b]) % 2 == 1:
        cnf.append([-idx[a], -idx[b]])
        nodd += 1
card = CardEnc.atleast(lits=list(idx.values()), bound=2 ** n, top_id=len(P), encoding=EncType.seqcounter)
cnf.extend(card.clauses)
fams = {F_M(n, M) for M in noncrossing_matchings(2 * n)}
print(f"n={n}: {len(P)} paths, {nodd} odd pairs, {len(fams)} noncrossing-matching families", flush=True)
t0 = time.time()
found = []
with Cadical153(bootstrap_with=cnf.clauses) as s:
    while s.solve():
        m = s.get_model()
        fam = frozenset(w for w in P if m[idx[w] - 1] > 0)
        found.append(fam)
        assert len(fam) >= 2 ** n
        # block exactly this family (any superset impossible by Thm 1.4)
        s.add_clause([-idx[w] for w in fam])
        if len(found) % 10 == 0:
            print(f"  {len(found)} families so far ({time.time()-t0:.0f}s)", flush=True)
print(f"n={n}: total maximum families found = {len(found)}; all are F_M: {all(f in fams for f in found)}; "
      f"count equals Catalan: {len(set(found)) == len(fams)}  ({time.time()-t0:.0f}s)")
