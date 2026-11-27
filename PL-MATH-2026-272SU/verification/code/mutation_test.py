"""
Mutation test for lemma_check.py: the checker must reject broken families.
  1) 20 families F_M (n = 5) with one word replaced by a path outside F_M;
  2) the size-2^n family of a crossing matching (not even).
usage: python3 mutation_test.py
"""
import random
import numpy as np
from lp import paths, edges, noncrossing_matchings, F_M
import lemma_check as L

rng = random.Random(0)
n = 5
P = paths(n)
caught = 0; total = 0
# 1) replace one word of an F_M by an outside word: family no longer extremal-even; Lemma 2 (b)/(c)/(E*) must fail somewhere
for M in list(noncrossing_matchings(2 * n))[:20]:
    F = sorted(F_M(n, M))
    out = [w for w in P if w not in F]
    G = sorted(F[1:] + [rng.choice(out)])
    W = np.array(G, dtype=np.int8); cc = L.common_cum(W)
    bad = any(not L.lemma2_general(G, cc, n, t, L.components(G, t), True)[0] for t in range(2 * n + 1))
    total += 1; caught += bad
print(f"word-swapped families rejected by Lemma 2 checks: {caught}/{total}")
# 2) a crossing matching family (size 2^n, not even): must fail
M = [(0, 2), (1, 3)] + [(2 * i, 2 * i + 1) for i in range(2, n)]
F = sorted(F_M(n, M))
W = np.array(F, dtype=np.int8); cc = L.common_cum(W)
print("crossing-matching family is even:", bool(np.all(cc[:, :, 2 * n] % 2 == 0)))
bad = any(not L.lemma2_general(F, cc, n, t, L.components(F, t), True)[0] for t in range(2 * n + 1))
print("crossing-matching family rejected by Lemma 2 checks:", bad)
try:
    L.check_extremal(n, M); print("check_extremal accepted crossing family (BAD)")
except AssertionError as e:
    print("check_extremal rejected crossing family:", e)
