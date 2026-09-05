# Erdős #287 effectivity — kernel bank report

All work is append-only.  Nothing existing was deleted, rewritten or downgraded.
**Erdős #287 is not claimed**; the joined square function, `C_joint ≤ 0.09`, the two-high
gap, medium-`k` closure, the signed floor and Maynard are untouched and unproved.

## Files added

| File | Content |
|---|---|
| `RequestProject/Erdos287/BsrcWeights.lean` | §2 physical `B_src` normalisation |
| `RequestProject/Erdos287/AllComplement.lean` | §3 all-complement discrete identity |
| `RequestProject/Erdos287/OddHalfDivisor.lean` | §5 odd half-divisor chart, §6 `w = 6` firewall |
| `RequestProject/Erdos287/Reflection.lean` | §9 half-divisor reflection |
| `RequestProject/Erdos287/MediumLedger.lean` | §7 full-vs-medium typing, §8 ledger-type firewall |
| `RequestProject/Erdos287/C1C2Splice.lean` | §10 discrete splice, §11 continuous splice |
| `RequestProject/Erdos287/OddLineCancellation.lean` | §12 odd line cancellation, §13 convolution |
| `RequestProject/Erdos287/RatioBoundary.lean` | §14 ratio-boundary form |
| `RequestProject/Erdos287/EulerLocal.lean` | §4 finite/conditional Euler identity, §15, §16, §18 |
| `RequestProject/Erdos287/TwoVariableZ.lean` | §17 two-variable identity, finite `Z(s,s) = 0` |
| `RequestProject/Erdos287/PerronAlgebra.lean` | §19 Perron variable change, §20 strict equality |
| `RequestProject/Erdos287/IncrementalDirectedLedger.lean` | §21 incremental ledger arithmetic |
| `RequestProject/Erdos287/CurrentStatusEffectivity.lean` | §22 open frontier, §23 axiom audit |

`RequestProject/Main.lean` gained the thirteen imports (the new modules are part of the
default build target).

## Conventions fixed where the specification was ambiguous

* **§10.**  The two lanes are `D₁ = ∑_d μ(d) ∑_{d<n≤Nb} T d n` and
  `D₂ = ∑_d μ(d) ∑_{2d<m≤Nb/2} T d (2m)`, i.e. the `c = 2` lane is the `n ↦ 2n`
  substituted lane; the endpoint `4d` for the even collar is then *derived*, not assumed.
* **§11.**  Mirroring §10, `C₂ = ∑_d μ(d) M_d ∫_{2d}^∞ W(2dt/X)dt`; both factors `1/2`
  come from `∫_{Ioi 2d} g(2t)dt = ½∫_{Ioi 4d} g`.
* **§17.**  `Z_P(u,v) = ∏_{p∈P}[1 + y_p/(p−2) − ((p−1)/(p−2))x_p] − ∏_{p∈P}(1 − x_p)`.
* **§4, §15.**  `B1loc(p) = p(p−2)/(p−1)²`; at `s = 0` the local ratio
  `(1 − 1/((p−1)p^s))/(1 − p^{-s-1})` equals exactly `B1loc(p)`, which is the precise sense
  in which the local numerator vanishes at `s = 0`.
* The oddness of `d` turned out **not** to be needed for the all-complement identity
  (the prime `2` never contributes); the odd form is recorded as a corollary.

## STRICT OUTPUT

```
PHYSICAL B1 NORMALIZATION:          KERNEL-PROVED
ALL-COMPLEMENT DISCRETE:            KERNEL-PROVED
CONTINUOUS EULER IDENTITY:          KERNEL-PROVED (finite) / CONDITIONAL (infinite)
ODD HALF-DIVISOR:                   KERNEL-PROVED
w = 6 FIREWALL:                     KERNEL-PROVED
FULL-vs-MEDIUM TYPING:              KERNEL-PROVED
INCREMENTAL LEDGER TYPE:            KERNEL-PROVED
HALF-DIVISOR REFLECTION:            KERNEL-PROVED
c1/c2 DISCRETE SPLICE:              KERNEL-PROVED
c1/c2 CONTINUOUS SPLICE:            KERNEL-PROVED (integrability hypothesis)
FULL ODD DISCRETE CANCELLATION:     KERNEL-PROVED
CONTINUOUS COEFFICIENT CONVOLUTION: KERNEL-PROVED
RATIO-BOUNDARY:                     KERNEL-PROVED (conditional on the two cancellations)
G_p LOCAL FACTOR:                   KERNEL-PROVED
FINITE B1*G(u,0)=1:                 KERNEL-PROVED
TWO-VARIABLE LOCAL EULER IDENTITY:  KERNEL-PROVED
FINITE Z(s,s)=0:                    KERNEL-PROVED
INFINITE Z(s,s)=0:                  BLOCKED BY ANALYTIC CONVERGENCE
G ABSOLUTE-CONVERGENCE REGION:      PARTIAL (v = 0 slice: |G_p(u,0) − 1| = 1/(p(p−2)) ≤ 3/p²)
PERRON VARIABLE CHANGE:             KERNEL-PROVED (algebra only)
STRICT EQUALITY ALGEBRA:            KERNEL-PROVED (conditional)
INCREMENTAL LEDGER ARITHMETIC:      KERNEL-PROVED
JOINED SQUAREFUNCTION:              OPEN
MEDIUM-k:                           OPEN
TWO-HIGH GAP:                       OPEN / NOT ENTERED
SIGNED FLOOR:                       OPEN
MAYNARD:                            NOT ENTERED
ERDOS287:                           OPEN
NO SORRY:                           YES
CUSTOM AXIOMS:                      NONE
LAKE BUILD:                         PASS (8450 jobs)
```

`#print axioms` is run on all fifty principal theorems in
`RequestProject/Erdos287/CurrentStatusEffectivity.lean`; every one reports either no axioms
or a subset of `propext, Classical.choice, Quot.sound`.  No `sorry`, `admit`, `axiom`,
`unsafe`, `native_decide`, `implemented_by` or `opaque` occurs in any new file.

## Isolated missing analytic inputs

1. Absolute convergence of `∏_p G_p(u,v)` on compacta of
   `{Re u > 0, Re v > −1/2, Re(u+v) > 0}`: needs the two-variable uniform majorant plus a
   `Summable ‖G_p − 1‖ → Multipliable G_p` criterion along the primes.
2. `∑ mOdd = 0` (i.e. `∑_{d odd} μ(d)/d = 0`): not proved; the downstream cancellation is
   stated conditionally on it and on the Cauchy-product identity.
3. A strict (half-jump) Perron theorem: §20 accepts it as an explicit hypothesis.
