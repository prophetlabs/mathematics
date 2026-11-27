"""
One-shot check of Conjecture 4.1 for a given n: is there a family of 2^n paths with pairwise even
edge-intersections that is different from every F_M (M noncrossing)?  UNSAT => the C_n families
F_M are all the extremal families.  usage: python3 sat_exclude.py n [solver]
"""
import sys, itertools, time
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from lp import paths, edges, noncrossing_matchings, F_M
n = int(sys.argv[1]); sname = sys.argv[2] if len(sys.argv) > 2 else 'cadical153'
P = paths(n); idx = {w: i + 1 for i, w in enumerate(P)}; E = {w: edges(w) for w in P}
cnf = CNF()
for a, b in itertools.combinations(P, 2):
    if len(E[a] & E[b]) % 2: cnf.append([-idx[a], -idx[b]])
card = CardEnc.atleast(lits=list(idx.values()), bound=2 ** n, top_id=len(P), encoding=EncType.totalizer)
cnf.extend(card.clauses)
fams = [F_M(n, M) for M in noncrossing_matchings(2 * n)]
for F in fams:                       # differ from F: some chosen path lies outside F
    cnf.append([idx[w] for w in P if w not in F])
print(f"n={n}: {len(P)} paths, {len(fams)} F_M excluded, solver={sname}", flush=True)
t0 = time.time()
with Solver(name=sname, bootstrap_with=cnf.clauses) as s:
    r = s.solve()
print(f"n={n}: {'SAT -- another extremal family exists!' if r else 'UNSAT -- every extremal family is some F_M'} ({time.time()-t0:.0f}s)", flush=True)
