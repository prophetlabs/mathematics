"""
Consistency check of the intermediate statements of the proof.

Part 1 (extremal families): for every noncrossing matching M of [2n], n <= N,
take F = F_M and check, at every split t:
  Lemma 2 (a), (b), (c), (E1), (E2), (E3);
  Lemma 3 (every (t-1)-component opens or closes, with the stated prefix and
           suffix sets and |A| = |A*|);
  Lemma 4 (before the first closing step everything opens, so the components
           are the 2^m singletons; segregation);
  Section 4.7 (no zigzag pair closes; every closing pair is a sibling pair with
           the heavier word taking E; every word has {w_{t-1}, w_t} = {N, E};
           deleting those positions gives F_{M'} with M = M' + {t-1, t}).
For n <= 6 the F_M are all the extremal families (sat_exclude.py), so this
checks every intermediate statement on every extremal family for those n.

Part 2 (non-extremal families): random maximal even families built greedily;
check Lemma 2 (a)-(c) at every t and the chain
  |F| <= sum |A_j||S_j| <= (sum |A_j|^2)^(1/2) (sum |S_j|^2)^(1/2),
  sum |A_j|^2 <= 2^t,  sum |S_j|^2 <= 2^(2n-t).

usage: python3 lemma_check.py N [random_trials_per_n]
"""
import sys, random, itertools
import numpy as np
from lp import paths, edges, noncrossing_matchings, F_M


def common_cum(W):
    """cc[a, b, s] = number of common edges of words a and b among their first s steps."""
    F, L = W.shape
    H = np.zeros((F, L + 1), dtype=np.int16)
    H[:, 1:] = np.cumsum(W, axis=1)
    E = (W[:, None, :] == W[None, :, :]) & (H[:, None, :L] == H[None, :, :L])
    cc = np.zeros((F, F, L + 1), dtype=np.int16)
    cc[:, :, 1:] = np.cumsum(E, axis=2)
    return cc


def components(words, t):
    """components of R_t, as lists of word indices (a word is an edge prefix--suffix)"""
    parent = list(range(len(words)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    seen_p, seen_s = {}, {}
    for i, w in enumerate(words):
        for key, seen in ((w[:t], seen_p), (w[t:], seen_s)):
            if key in seen:
                parent[find(i)] = find(seen[key])
            else:
                seen[key] = i
    groups = {}
    for i in range(len(words)):
        groups.setdefault(find(i), []).append(i)
    return list(groups.values())


def lemma2_general(words, cc, n, t, comps, extremal):
    """Lemma 2 (a)-(c), and (E1)-(E3) if extremal. Returns (ok, sumA2, sumS2, sumAS)."""
    L = 2 * n
    lab = np.empty(len(words), dtype=np.int32)
    for j, comp in enumerate(comps):
        lab[comp] = j
    rep = np.array([comp[0] for comp in comps])
    Pt = cc[:, :, t] % 2                  # c(prefixes) mod 2
    Ps = (cc[:, :, L] - cc[:, :, t]) % 2  # c*(suffixes) mod 2
    same = lab[:, None] == lab[None, :]
    ok = True
    # (b) inside a component: c = c* = t (mod 2)
    ok &= bool(np.all(Pt[same] == t % 2)) and bool(np.all(Ps[same] == t % 2))
    # (c) across components: constant on A_j x A_k, on S_j x S_k, and the two constants equal
    V = Pt[np.ix_(rep[lab], rep[lab])]
    ok &= bool(np.all((Pt == V) | same)) and bool(np.all((Ps == V) | same))
    sumA2 = sumS2 = sumAS = 0
    for comp in comps:
        A = {words[i][:t] for i in comp}
        S = {words[i][t:] for i in comp}
        ok &= len({sum(x) for x in A}) == 1 and len({sum(y) for y in S}) == 1   # (a)
        sumA2 += len(A) ** 2
        sumS2 += len(S) ** 2
        sumAS += len(A) * len(S)
        if extremal:
            ok &= len(comp) == len(A) * len(S)               # (E1)
            ok &= len(S) * 2 ** t == 2 ** n * len(A)         # (E2)
    ok &= sumA2 <= 2 ** t and sumS2 <= 2 ** (L - t)          # Lemma 1 on both sides
    ok &= len(words) <= sumAS and sumAS ** 2 <= sumA2 * sumS2
    if extremal:
        ok &= sumA2 == 2 ** t                                # (E3)
    return ok, sumA2, sumS2, sumAS


def check_extremal(n, M):
    F = sorted(F_M(n, M))
    L = 2 * n
    W = np.array(F, dtype=np.int8)
    cc = common_cum(W)
    assert len(F) == 2 ** n and np.all(cc[:, :, L] % 2 == 0), "F_M not extremal"
    comps = [components(F, t) for t in range(L + 1)]
    for t in range(L + 1):
        assert lemma2_general(F, cc, n, t, comps[t], True)[0], f"Lemma 2 fails n={n} M={M} t={t}"
    first_close = None
    for t in range(1, L + 1):
        prev, cur = comps[t - 1], comps[t]
        cur_of = {}
        for j, comp in enumerate(cur):
            for i in comp:
                cur_of[i] = j
        closes = []
        for K in prev:
            letters = {F[i][t - 1] for i in K}
            if len(letters) == 2:  # opens
                for a in (0, 1):
                    part = [i for i in K if F[i][t - 1] == a]
                    js = {cur_of[i] for i in part}
                    assert len(js) == 1 and sorted(cur[js.pop()]) == sorted(part), "Lemma 3 (open)"
            else:
                closes.append(K)
        partner = {}
        for K in closes:
            (j,) = {cur_of[i] for i in K}
            Kp = cur[j]
            rest = sorted(set(Kp) - set(K))
            others = [K2 for K2 in closes if K2 is not K and sorted(K2) == rest]
            assert len(others) == 1, "Lemma 3 (close: exactly one partner)"
            K2 = others[0]
            a = F[K[0]][t - 1]
            b = F[K2[0]][t - 1]
            assert a != b, "Lemma 3 (close: other letter)"
            A, A2 = {F[i][:t - 1] for i in K}, {F[i][:t - 1] for i in K2}
            S, S2 = {F[i][t - 1:] for i in K}, {F[i][t - 1:] for i in K2}
            assert len(A) == len(A2), "Lemma 3 (close: |A| = |A*|)"
            assert {y[1:] for y in S} == {y[1:] for y in S2}, "Lemma 3 (close: common S')"
            assert len({sum(x) + a for x in A} | {sum(x) + b for x in A2}) == 1, "Lemma 3 (N-count)"
            partner[id(K)] = K2
        if closes and first_close is None:
            first_close = t
            m = t - 1
            # Lemma 4: the (t-1)-components are the 2^m singletons
            pre = [{F[i][:m] for i in K} for K in prev]
            assert all(len(p) == 1 for p in pre) and len(pre) == 2 ** m, "Lemma 4 (singletons)"
            closer = {next(iter(p)) for p, K in zip(pre, prev) if K in closes}
            opener = {next(iter(p)) for p, K in zip(pre, prev) if K not in closes}
            # segregation
            assert not ({sum(x) for x in closer} & {sum(x) for x in opener}), "Lemma 4(a)"
            for K in closes:
                x = F[K[0]][:m]
                x2 = F[partner[id(K)][0]][:m]
                assert x[:-1] == x2[:-1], f"closing pair not siblings: {x}, {x2}"
                heavier = x if sum(x) > sum(x2) else x2
                hv = [i for i in K + partner[id(K)] if F[i][:m] == heavier]
                assert all(F[i][t - 1] == 0 for i in hv), "heavier sibling must take E"
            assert not opener, "Step 2: every word of length m is a closer"
    t = first_close
    assert t is not None and t >= 2
    assert all(w[t - 2] != w[t - 1] for w in F), "Step 2: flippable pair"
    swap = {w[:t - 2] + (w[t - 1], w[t - 2]) + w[t:] for w in F}
    assert swap == set(F), "Step 2: swap invariance"
    contracted = {w[:t - 2] + w[t:] for w in F}
    assert (t - 2, t - 1) in [tuple(sorted(p)) for p in M], "first closing step is not an adjacent pair of M"
    Mp = []
    for a, b in M:
        if {a, b} == {t - 2, t - 1}:
            continue
        sh = lambda v: v if v < t - 2 else v - 2
        Mp.append((sh(a), sh(b)))
    assert contracted == set(F_M(n - 1, Mp)), "Step 3: contraction is F_{M'}"
    return t


def random_even_family(n, P, E, rng):
    order = P[:]
    rng.shuffle(order)
    fam = []
    for w in order:
        if all(len(E[w] & E[v]) % 2 == 0 for v in fam):
            fam.append(w)
    return fam


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    for n in range(1, N + 1):
        Ms = list(noncrossing_matchings(2 * n))
        firsts = [check_extremal(n, M) for M in Ms]
        print(f"n={n}: all {len(Ms)} F_M pass Lemmas 2-4 and Steps 1-3 "
              f"(first closing step t ranges over {sorted(set(firsts))})", flush=True)
    rng = random.Random(1)
    for n in range(2, N + 1):
        P = paths(n)
        E = {w: edges(w) for w in P}
        sizes = []
        for _ in range(trials):
            fam = sorted(random_even_family(n, P, E, rng))
            sizes.append(len(fam))
            W = np.array(fam, dtype=np.int8)
            cc = common_cum(W)
            for t in range(2 * n + 1):
                ok = lemma2_general(fam, cc, n, t, components(fam, t), len(fam) == 2 ** n)[0]
                assert ok, f"Lemma 2 fails on a random even family n={n} t={t}"
        print(f"n={n}: {trials} random maximal even families (sizes {min(sizes)}..{max(sizes)}, "
              f"{sum(s == 2 ** n for s in sizes)} of size 2^n) pass Lemma 2 (a)-(c) and the bound chain",
              flush=True)
