# PL-MATH-2026-272SU — verification files

Verification material for the PROPHET LABS paper **Even-Intersecting Families of Lattice Paths and the
Catalan Numbers: A Proof of Shankar's Conjecture 4.1** ([`../paper.pdf`](../paper.pdf)).

**Status: UNDER_REVIEW.** The proof is complete. The PROPHET LABS pipeline Lean check (`prophet lean check`) passed, and the main count compiles with only
Lean's standard axioms. In the PROPHET LABS status scheme, PROVEN and FORMALLY_VERIFIED both also require an
independent adversarial review, and that review has not been carried out yet.

| Folder | Contents |
| --- | --- |
| [`lean/`](lean/) | Lean 4 + Mathlib formalization: 11 files, 2,437 lines. The main theorem is `OC.conjecture_4_1`. |
| [`code/`](code/) | Python scripts for the exhaustive and SAT checks, with logs of the completed runs. |

## The formal statement

```lean
theorem OC.conjecture_4_1 (n : ℕ) :
    {F ∈ (Omega n).powerset |
      (∀ w ∈ F, ∀ v ∈ F, w ≠ v → Even (edges w ∩ edges v).card) ∧ F.card = 2 ^ n}.card
      = catalan n
```

`#print axioms OC.conjecture_4_1` reports `propext`, `Classical.choice` and `Quot.sound` only. The
development contains no `sorry`, `admit` or `native_decide`. See [`lean/README.md`](lean/README.md) for the
file map and build instructions.

## Computations (`code/`)

Python 3.13 with `networkx`, `numpy` and `python-sat`. Run each script from inside `code/`.

| Command | What it checks | Result |
| --- | --- | --- |
| `python3 lp.py 5` | All extremal families, by maximum-clique enumeration | 1, 2, 5, 14, 42 families for n ≤ 5, all of the form F_M |
| `python3 sat_count.py 5` | Independent SAT enumeration of all extremal families | 14 for n = 4, 42 for n = 5 |
| `python3 sat_exclude.py 6` | One SAT call: is there an extremal family other than the F_M? | UNSAT for n = 5 and n = 6 (n = 6 takes about 41 minutes); log `excl6.log` |
| `python3 classC.py 10`, `python3 sibling_check.py 11` | Theorem 3.3 (pairs satisfying the parity condition) | Only sibling pairs and the zigzag pair, m ≤ 10 (m ≤ 11 for N-count difference 1) |
| `python3 lemmaD_check.py 11` | Lemma 4.5 | Exactly the stated pairs, k ≤ 11 |
| `python3 lemma_check.py 8 100` | Every intermediate statement of the proof on every F_M, and Lemma 4.2(a)–(c) on random non-extremal families | All hold for n ≤ 8; log `lemma_check.log` |
| `python3 mutation_test.py` | The checker above rejects broken families | Rejects all 20 word-swapped families and a crossing-matching family |

`sat6.log` records the SAT enumeration for n = 6, which was stopped at 130 families (all F_M) once
`sat_exclude.py 6` had settled the case.

## Not verified

- No independent review, human or automated, has been carried out.
- The Lean development proves the classification in insertion-family form. Identifying insertion families
  with the families F_M is a standard argument that is not formalized; the count does not depend on it.
- The Lean files were compiled against an existing Mathlib build; a from-scratch `lake build` was not run.
