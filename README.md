# Erdős Problem #287 — Lean-Verified Finite Reduction and Clean Public Review

**Status:** partial formal verification / public research draft.  
**This repository does not claim an unconditional proof of Erdős #287.**

## Start here

- [Clean public review — current V16](ERDOS287_PUBLIC_REVIEW_CURRENT.pdf)
- [Legacy forum PDF path — same current V16 content](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)
- [Clean V16 LaTeX source](ERDOS287_PUBLIC_REVIEW_V16_CLEAN.tex)
- [V16 consolidation audit](ERDOS287_V16_CLEAN_CONSOLIDATION_AUDIT.md)
- [Current technical verification ledger](ERDOS287_TECHNICAL_VERIFICATION_LEDGER_CURRENT.md)

The former V15 chronological patch stack is preserved immutably:

- [V15 technical dossier archive](archive/ERDOS287_TECHNICAL_DOSSIER_V15_PATCHSTACK.pdf)
- [V15 source archive](archive/PUBLIC_REVIEW_DRAFT15_PATCHSTACK.tex)

## What is publicly Lean-checked

- exact Erdős-287 counterexample predicate;
- ordered public-statement compiler;
- top-layer / adjacent-hole / prime-power window obstruction;
- no exact counterexample with maximum denominator at most `4,000,000,000`;
- exact `WindowPairSupply` predicate;
- end-to-end conditional compiler from eventual `WindowPairSupply`;
- V14 finite/algebraic Vaughan source spine.

## What is not yet publicly Lean-replayed

The supplied midpoint Aristotle archive contains V15 `Λ=μ*log`, determinant-one-line, and balanced-seven polarization source. At the V16 audit cutoff those files were not yet on public `main`, and the ongoing V15 replay was not independently rerun in the present environment. The clean paper therefore labels them:

```text
FORMALIZATION SOURCE PRESENT — PUBLIC REPLAY PENDING
```

rather than `PUBLIC LEAN-CHECKED`.

## Current research frontier

The source-minimal affine identity is

```math
Λ(2mn+s)=Σ_{qr=2mn+s} μ(q)log r,
```

with a hard determinant-one line `qr-2mn=s`.

For the balanced-seven cell at

```text
Q=X^(3/5), Y=X^(1/7),
```

squarefree torus polarization reduces the current V-branch to two explicit open inputs:

```text
AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45
```

The remaining hard μ-log cells, fixed-certificate packet census, FCL, positive prime/almost-prime mass, and eventual `WindowPairSupply` are also open.

## Exact formal remaining global interface

`Erdos287.WindowPairSupply M` asks for two adjacent positions in the top half of `[1,M]`, each carrying a prime-power divisor whose window is at most `9` and whose prime base exceeds the certified numerator bound.

The public Lean theorem proves:

```text
effective eventual WindowPairSupply
+ finite exclusion through 4e9
=> Erdős #287.
```

No eventual supply theorem is proved here.

## Reproducibility and trust boundary

The V16 paper and its two stable PDF filenames are generated from one clean LaTeX source by GitHub Actions. The source commit is printed inside the PDF.

AI assistance: the project used Aristotle and LLM-assisted mathematical research. Every public claim is stated at the proof-status level indicated in the paper and ledger.
