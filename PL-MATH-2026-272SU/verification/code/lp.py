"""
Even-intersecting families of North-East lattice paths (0,0)->(n,n).
Conjecture 4.1 of U. Shankar, arXiv:2607.23117:
   the families of size 2^n with pairwise even edge-intersections are exactly
   F_M = { w : w_i != w_j for every {i,j} in M },  M a noncrossing perfect matching of [2n].
"""
import itertools, sys


def paths(n):
    out = []
    for pos in itertools.combinations(range(2 * n), n):
        w = [0] * (2 * n)
        for p in pos:
            w[p] = 1  # 1 = N, 0 = E
        out.append(tuple(w))
    return out


def edges(w):
    x = y = 0
    E = set()
    for i, c in enumerate(w):
        if c:
            E.add((x, y, 'N')); y += 1
        else:
            E.add((x, y, 'E')); x += 1
    return frozenset(E)


def common(w, v):
    return len(edges(w) & edges(v))


def noncrossing_matchings(m):
    """all noncrossing perfect matchings of [0..m-1]"""
    if m == 0:
        yield []
        return
    for j in range(1, m, 2):
        for left in noncrossing_matchings(j - 1):
            for right in noncrossing_matchings(m - j - 1):
                yield [(0, j)] + [(a + 1, b + 1) for a, b in left] + [(a + j + 1, b + j + 1) for a, b in right]


def F_M(n, M):
    out = []
    for bits in itertools.product([0, 1], repeat=n):
        w = [None] * (2 * n)
        for (a, b), s in zip(M, bits):
            w[a] = s
            w[b] = 1 - s
        out.append(tuple(w))
    return frozenset(out)


if __name__ == "__main__":
    import networkx as nx
    for n in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 5):
        P = paths(n)
        E = {w: edges(w) for w in P}
        G = nx.Graph()
        G.add_nodes_from(P)
        for a, b in itertools.combinations(P, 2):
            if len(E[a] & E[b]) % 2 == 0:
                G.add_edge(a, b)
        maxc = [frozenset(c) for c in nx.find_cliques(G) if len(c) >= 2 ** n]
        big = max(len(c) for c in nx.find_cliques(G))
        fams = {F_M(n, M) for M in noncrossing_matchings(2 * n)}
        print(f"n={n}: max clique size {big} (2^n={2**n}); #cliques of size 2^n = {len(set(maxc))}; "
              f"#F_M = {len(fams)}; equal sets: {set(maxc) == fams}", flush=True)
