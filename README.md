# PROPHET LABS — Mathematics

*Solving What Remains Unsolved.*

PROPHET LABS is an AI-assisted mathematical research operation. This repository publishes its papers on open
problems, each with everything needed to check it: the paper itself, formal Lean 4 proofs where they exist,
and the code behind every computational claim.

## Papers

| ID | Title | Result | Status |
| --- | --- | --- | --- |
| [PL-MATH-2026-272SU](PL-MATH-2026-272SU/) | Even-Intersecting Families of Lattice Paths and the Catalan Numbers: A Proof of Shankar's Conjecture 4.1 | Proof of [Conjecture 4.1 of arXiv:2607.23117](https://arxiv.org/abs/2607.23117): exactly Cₙ families of 2ⁿ lattice paths with pairwise even edge-intersections | UNDER_REVIEW: count verified in Lean 4; independent review not completed |

## Layout

Each paper has its own folder, named by its ID (`PL-MATH-YYYY-XXXXX`):

```
PL-MATH-YYYY-XXXXX/
├── paper.pdf
└── verification/
    ├── README.md   what was checked, and how to reproduce it
    ├── lean/       Lean 4 + Mathlib formalization (when there is one)
    └── code/       scripts for every computational claim
```

## Verification status

Every paper states exactly what has been checked. The statuses mean:

| Status | Meaning |
| --- | --- |
| UNDER_REVIEW | A complete argument exists, but the independent adversarial review is not yet complete. |
| PROVEN | A complete proof that passed independent adversarial review, counterexample search and boundary analysis. |
| DISPROVEN | An exactly verified counterexample, independently reviewed. |
| FORMALLY_VERIFIED | A Lean 4 + Mathlib proof that compiles with no `sorry` and only Lean's standard axioms, independently confirmed to state the intended result. |

A computer search on finite cases is reported as evidence, never as a proof of a general statement.

## How the work is produced

Problem selection, computation, proof construction and drafting are carried out by AI research agents under a
documented verification protocol. No AI system is listed as an author; responsibility for the content rests
with PROPHET LABS. The papers are not peer-reviewed. Corrections and counterexamples are welcome: please open
an issue.
