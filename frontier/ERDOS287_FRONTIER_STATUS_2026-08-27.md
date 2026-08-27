# Erdős Problem #287 — Research Frontier (27 Aug 2026)

**Status: OPEN problem / research frontier. This repository does not claim a proof of Erdős #287 or twin-prime infinitude.**

This frontier snapshot accompanies the standalone verification dossier:

- `ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.pdf`
- `ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.tex`
- `ERDOS287_ARISTOTLE_V12_SMOOTH_PARITY_REPROOF.md`

## What is currently firm

The finite Erdős-287 compiler remains the strongest formal component of the repository. The current research dossier also records:

- an explicit fixed Ford-certificate route and a finite transference identity;
- the corrected separation of total correlation, fixed leakage, and the exceptional `N2` contribution;
- a generic seven-prime quadratic-Kummer bilinear estimate as a **conditional child provider**;
- the fact that the fixed-certificate packet census is **not** exhausted by H8/H9.

## First literal analytic open in the fixed-certificate route

The first source-exact uncovered packet is the smooth Möbius-parity correlation

```text
P_sm(X) = sum_{X/2<n<=X, P+(n)<=n^sigma*}
          W(n/X)[Lambda(2n-1)+Lambda(2n+1)-4B(n)]
          * sum_{d|n, d<=n^(1/2-epsilon*)} mu(d).
```

Programme label:

`287-FIXED-CERTIFICATE-SMOOTH-PARITY45`

A certificate-compatible constant saving would suffice; arbitrary-log saving is stronger than logically necessary.

## Important counterguard

For balanced squarefree `k`-prime cells, the truncated Möbius weight can be

```text
H_*(n) = (-1)^r * binom(k-1,r) != 0,
r = floor(k*gamma_*).
```

Therefore defect orders above 9 occur literally. In particular:

`FINITE-H8/H9-ONLY-CENSUS = FAIL`.

The seven-prime Kummer estimate remains useful for packets that are source-exactly reduced to its quadratic-Kummer model, but it does not close the full fixed-certificate leakage family.

## Current honest dependency picture

```text
explicit fixed Ford certificate g*
+ fixed-certificate transference
        |
        v
287-FIXED-CERTIFICATE-SMOOTH-PARITY45
+ other literal fixed-g* packets
        |
        v
source-exhaustive regrouping
or a new direct smooth-parity theorem
        |
        v
287-FIXED-CERTIFICATE-LEAKAGE45
+ Gate 0 / comparison / N2
        |
        v
positive affine prime mass
        |
        v
finite Erdős-287 blocker
+ effectivity / finite bridge
        |
        v
Erdős #287
```

The universal Ford–Maynard Type-II route and the proof-specific generated-(7.23) route remain valid sufficient alternatives.

## Formal / research firewall

Do not promote any of the following into the trusted Lean result merely from this research note:

- `287-FIXED-CERTIFICATE-SMOOTH-PARITY45`;
- `287-FIXED-CERTIFICATE-LEAKAGE45`;
- H8/H9 source-to-Kummer closure;
- universal Ford–Maynard Type II;
- the final theorem Erdős #287.

The accompanying Aristotle prompt is explicitly hostile/append-only and forbids `sorry`, `admit`, or new axioms.
