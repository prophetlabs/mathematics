# Lean 4 formalization — PL-MATH-2026-272SU

A machine-checked proof, in Lean 4 with Mathlib, of Conjecture 4.1 of U. Shankar, *Oddtown and eventown
theorems for lattice paths* (arXiv:2607.23117). The paper is [`../../paper.pdf`](../../paper.pdf).

```lean
theorem OC.conjecture_4_1 (n : ℕ) :
    {F ∈ (Omega n).powerset |
      (∀ w ∈ F, ∀ v ∈ F, w ≠ v → Even (edges w ∩ edges v).card) ∧ F.card = 2 ^ n}.card
      = catalan n
```

There are exactly C_n families of 2^n North-East lattice paths from (0,0) to (n,n) in which every two
distinct paths share an even number of unit edges. `#print axioms OC.conjecture_4_1` reports only
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, `admit`, `native_decide` or added
axiom.

## Definitions

| Lean | Meaning |
| --- | --- |
| `List Bool` | a lattice path as a word: `true` = N (step up), `false` = E (step right) |
| `Omega n` | words of length 2n with exactly n letters N: the paths from (0,0) to (n,n) |
| `edges w` | the unit edges of the path from the origin, as pairs (start point, direction) |
| `catalan n` | Mathlib's Catalan numbers |

The proof works with a recursive count `c x y` of common edges; `OC.c_eq_card_inter` proves
`c x y = (edges x ∩ edges y).card`, so the theorem is stated in terms of geometric edges.

## Files and the results they prove

| File | Content | Paper |
| --- | --- | --- |
| `OC/Basic.lean` | words, N-count, common edges `c`; splitting and appending letters | Section 2, (2.1)–(2.2), Fact 2.5 |
| `OC/ThmC.lean` | `OC.thmC`, `OC.lemD`, proved together by induction | Theorem 3.3, Lemma 4.5 |
| `OC/Lemma1.lean` | `OC.lemma1`: the square-sum bound at any length | Lemma 4.1 |
| `OC/Lemma2.lean` | splitting parity, signature classes, suffixes via reversal | Lemma 4.2 |
| `OC/Bound.lean` | `OC.EvenFam.card_le` (Shankar's bound) and `OC.EvenFam.structure` ((E1)–(E3)) | Theorem 2.2, Lemma 4.2 |
| `OC/Prefix.lean` | prefixes and extensions; one prefix per class when all prefixes occur | Sections 4.3–4.4 |
| `OC/Closing.lean` | closing pairs: existence, uniqueness, parity condition, segregation | Lemmas 4.3–4.4 |
| `OC/Steps.lean` | `OC.Ctx.no_zigzag` and `OC.Ctx.all_siblings` | Section 4.6, Steps 1–2 |
| `OC/Main.lean` | `OC.c_ins`, `OC.cat_extremal`, `OC.extremal_cat`, `OC.extremal_iff_cat` | Facts 2.6–2.7, Step 3, Theorem 3.1 |
| `OC/Edges.lean` | `OC.c_eq_card_inter` | (2.1) |
| `OC/Count.lean` | the Catalan count and `OC.conjecture_4_1` | Corollary 3.2 |
| `Check.lean` | prints the main statements and their axioms | |

The formal proof is organised slightly differently from the paper, as described in Section 5.1 of the
paper: classes are defined by a signature rather than as connected components; Lemma 4.3 is used only at the
first closing step; and the extremal families are characterised as insertion families (`OC.Cat`), from which
the count follows by the Catalan recursion. Identifying insertion families with Shankar's families F_M is
standard and not formalized; the count does not use it.

## Building

The files were compiled with Lean 4.36.0 against Mathlib tag `v4.36.0` (commit `fc4f59e5`).

1. Put the `LEAN_PATH` of a Mathlib `v4.36.0` build into a file named `.leanpath` in this folder. From inside
   any Lake project that depends on that Mathlib: `lake env printenv LEAN_PATH > <this folder>/.leanpath`.
2. Run `./build.sh`. It compiles `OC/*.lean` in dependency order into `build/` (about 75 seconds) and runs
   `Check.lean`, which prints the main statements and their axioms.

`./mk.sh OC/Count` compiles a single module. `lakefile.toml` and `lean-toolchain` declare the same
dependency for `lake build`; that route has not been tested.
