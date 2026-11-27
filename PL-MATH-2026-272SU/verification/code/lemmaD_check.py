# Brute-force check of Lemma D: pairs (y,y') of k-step paths with P(y') = P(y) + (2,-2) such that
# c(p,y) = c(p,y') (mod 2) for every k-step p NOT ending at the midpoint Z = P(y) + (1,-1).
# Claim: solutions exist only for even k = 2s+2, and then (y,y') = (N(NE)^s N, E(EN)^s E).
import itertools, sys
def edgeset(w):
    x=y=0; E=set()
    for c in w:
        if c: E.add((x,y,1)); y+=1
        else: E.add((x,y,0)); x+=1
    return frozenset(E)
def show(w): return ''.join('N' if c else 'E' for c in w)
for k in range(1, int(sys.argv[1])+1):
    W=list(itertools.product((0,1),repeat=k)); ES={w:edgeset(w) for w in W}; wt={w:sum(w) for w in W}
    sols=[]
    for y in W:
        for yp in W:
            if wt[y]!=wt[yp]+2: continue
            zw=wt[y]-1                      # weight of paths ending at Z
            if all((len(ES[p]&ES[y])+len(ES[p]&ES[yp]))%2==0 for p in W if wt[p]!=zw):
                sols.append((show(y),show(yp)))
    exp=[]
    if k%2==0:
        s=(k-2)//2; exp=[('N'+'NE'*s+'N','E'+'EN'*s+'E')]
    print(f"k={k}: solutions={sols}  expected={exp}  match={sols==exp}", flush=True)
