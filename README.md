# Erdős Problem #287 — Gate 0–2 Theory Manual / Current R7 Post-Audit Frontier

**Status:** public research draft / partial formal verification.  
**This repository does not claim an unconditional proof of Erdős #287.**

## Start here

- [Current public review — V16.6 R7 post-audit theory manual](ERDOS287_PUBLIC_REVIEW_CURRENT.pdf)
- [Legacy forum PDF path — same current R7 content](ERDOS287_PUBLIC_REVIEW_DRAFT_V2_FINAL.pdf)
- [Immutable R7 PDF](ERDOS287_PUBLIC_REVIEW_V16_6_R7_POSTAUDIT_BALANCED7.pdf)
- [R7 LaTeX source](ERDOS287_PUBLIC_REVIEW_V16_6_R7_POSTAUDIT_BALANCED7.tex)
- [R5 -> R7 change log](ERDOS287_R5_TO_R7_CHANGELOG.md)
- [R7 hostile consistency check](ERDOS287_V16_6_R7_HOSTILE_CONSISTENCY_CHECK.md)

Immutable earlier R4/R5 public versions remain in repository history / named files.

## Unconditional theorem and global compiler

The machine-checked finite theorem excludes every exact counterexample with maximum denominator

```text
M <= 4,000,000,000.
```

The exact conditional large-`M` interface remains `Erdos287.WindowPairSupply`. No eventual supply theorem is claimed proved.

## Current Balanced7 status

The controlling source is the direct fixed-certificate SP-2 seven-prime cell.  Its literal source has

```text
H_*(P) = -20,
Lambda(2P+s) = sum_{qr=2P+s} mu(q) log r,
C_ext = 1.
```

The completed hostile audit now records research-level passes for:

```text
full-q Euler principal uniformity;
SmallQ 3+4 conductor-split multiplicative large sieve;
general-modulus SmallR large sieve and owner subtraction;
physical hard range delta = 1/21;
short-t upper sieve + Shiu divisor average;
ALL-Q-NO-DOUBLE-SPENDING45;
ALL-Q-PROVIDER-REASSEMBLY45.
```

Accordingly:

```text
SP2-BALANCED7-FULL-Q45:
    CLOSED AT CURRENT RESEARCH/PAPER LEVEL.

BALANCED7:
    HOSTILE-AUDITED RESEARCH/PAPER PASS,
    subject to exact literal SP-2 source sealing in this manuscript repository.
```

This is **not** an effective theorem: the SmallQ low-conductor argument presently uses classical Siegel–Walfisz, whose threshold is generally ineffective.

## Main next frontier

```text
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45:
    OPEN / NEXT PARENT.

287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45:
    OPEN / CANDIDATE FIRST CHILD.

287-EFFECTIVE-LOWCOND-EXCEPTIONAL-PNT45:
    OPEN EFFECTIVITY LANE.
```

FCL remains open; `N2` and Gate 2 are not yet activated; eventual `WindowPairSupply` remains open.

## Formal provenance

Public aggregate `RequestProject/Main.lean` is verified through the V15–V19 banks.  A later supplied safe-bank report records an 8213-job zero-error build for post-Balanced7 source/compiler modules, but those named modules are not presently aggregate-synchronized in this manuscript repository.  R7 therefore labels that layer:

```text
SUPPLIED LEAN SAFE BANK / REPOSITORY SYNC PENDING.
```

External multiplicative-large-sieve, one-dimensional upper-sieve and Shiu inputs are not described as Lean analytic theorems.

## Global firewall

```text
Balanced7 research closure !=> effective Balanced7.
Balanced7 !=> FCL.
FCL !=> WindowPairSupply.
Gate providers !=> generated Full Type II without source exhaustiveness.
No local analytic packet closure alone proves Erdős #287.
```

**ERDŐS PROBLEM #287 REMAINS OPEN.**
