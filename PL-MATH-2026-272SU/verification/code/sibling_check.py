"""
Brute-force check of the 'sibling lemma':
  m >= 1, x, x' in {0,1}^m with wt(x) = wt(x') + 1.  If c(p,x) = c(p,x') (mod 2)
  for every p in {0,1}^m whose endpoint differs from both endpoints of x and x',
  then x and x' agree in their first m-1 letters.
c = number of common edges of the two lattice paths (1 = N, 0 = E).
"""
import itertools, sys

def edgeset(w):
    x = y = 0; E = set()
    for c in w:
        if c: E.add((x, y, 1)); y += 1
        else: E.add((x, y, 0)); x += 1
    return E

for m in range(1, int(sys.argv[1]) + 1):
    W = list(itertools.product((0, 1), repeat=m))
    ES = {w: edgeset(w) for w in W}
    wt = {w: sum(w) for w in W}
    bad = []
    npairs = 0
    for x in W:
        for xp in W:
            if wt[x] != wt[xp] + 1:
                continue
            npairs += 1
            ok = True
            for p in W:
                if wt[p] in (wt[x], wt[xp]):
                    continue        # endpoint at level m is determined by the weight
                if (len(ES[p] & ES[x]) + len(ES[p] & ES[xp])) % 2:
                    ok = False; break
            if ok and x[:-1] != xp[:-1]:
                bad.append((x, xp))
    print(f"m={m}: pairs tested {npairs}, hypothesis holds but not siblings: {len(bad)}", bad[:5], flush=True)
