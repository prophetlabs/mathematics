# Enumerate C_m = { unordered pairs {x,x'} of m-step paths : c(p,x) = c(p,x') (mod 2) for all
# m-step p whose endpoint differs from both endpoints }.  Classify by endpoint offset and shape.
import itertools, sys
from collections import Counter
def edgeset(w):
    x=y=0; E=set()
    for c in w:
        if c: E.add((x,y,1)); y+=1
        else: E.add((x,y,0)); x+=1
    return frozenset(E)
def show(w): return ''.join('N' if c else 'E' for c in w)
for m in range(1, int(sys.argv[1])+1):
    W=list(itertools.product((0,1),repeat=m)); ES={w:edgeset(w) for w in W}; wt={w:sum(w) for w in W}
    sols=[]
    for i,x in enumerate(W):
        for xp in W[i+1:]:
            ok=True
            for p in W:
                if wt[p] in (wt[x],wt[xp]): continue
                if (len(ES[p]&ES[x])+len(ES[p]&ES[xp]))%2: ok=False;break
            if ok: sols.append((x,xp))
    kinds=Counter()
    ex=[]
    for x,xp in sols:
        d=abs(wt[x]-wt[xp])
        k=next(i for i in range(m) if x[i]!=xp[i])+1   # first differing position
        sib = (x[:-1]==xp[:-1])
        kinds[(d, 'sib' if sib else f'first_diff@{k}')]+=1
        if not sib and len(ex)<6: ex.append((show(x),show(xp),d))
    print(f"m={m}: {len(sols)} pairs; kinds={dict(kinds)}; non-sibling examples={ex}", flush=True)
