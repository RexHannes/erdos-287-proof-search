# Erdős Problem #287 — Authoritative Current Status

**Checkpoint:** 2 September 2026  
**Public verdict:** **ERDŐS #287: OPEN.**

This file is the controlling concise status ledger. Historical R4/R5/R7/R9 manuscripts and earlier status files remain preserved for provenance. The latest public-review research delta is [`ERDOS287_PUBLIC_REVIEW_R10_02SEP_TWO_LANE_FCL_DELTA.md`](ERDOS287_PUBLIC_REVIEW_R10_02SEP_TWO_LANE_FCL_DELTA.md).

## Unconditional / formal bank

- The machine-checked finite exclusion through maximum denominator `M <= 4,000,000,000` is unchanged.
- Existing Lean/Aristotle safe banks remain valid only under their stated hypotheses.
- Paper/research analytic closure is **not** silently promoted to Lean theoremhood. Explicit analytic/source interfaces remain uninhabited unless a dependency-complete formal proof has actually been supplied.

## Paper/research bank now closed

The following are banked at the paper/research level under their exact source dictionaries:

```text
287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45          [for already-typed packets]
GLOBAL-BSRC-COMPARISON-MARGIN45              [asymptotic]
N1-BSRC-DICTIONARY                           [asymptotic]
E_M = o(B_X)                                 [asymptotic]
FIXEDCERTIFICATE-N2-LAMBDA-COLLAR45          [fixed-epsilon asymptotic]
FOUR-ERROR FIXED-CERTIFICATE TRANSFERENCE
FCL_W(M/2) -> WindowPairSupply(M), M >= 12
```

### Physical N2 Lambda collar

The physical von Mangoldt-weighted `N_2` source is handled directly; the Ford bounded-sequence shortcut is not used. The banked result is

```math
E_2/B_X <= K_collar * epsilon + o(1),
```

and for one fixed sufficiently small `epsilon`, eventually

```math
E_2 <= (m_epsilon/8) B_X.
```

No explicit numerical `epsilon`, `K_collar`, or large-`X` threshold is claimed yet.

### Bsrc / N1 / comparison margin

The physical comparison is

```math
B_src(n)=S_2\prod_{p|n,\,p>2}(p-1)/(p-2),
```

with

```math
b_X(n)=4W(n/X)B_src(n).
```

The latest source audit gives

```math
E_M=o(B_X),
```

and

```math
B_X=(4S_2\int W+o(1))X/log X.
```

The Ford limiting margin satisfies `m_0 >= 6e-6`, and the support-truncated perturbed certificate has positive margin for sufficiently small fixed `epsilon`.

## Exact four-error FCL algebra

The controlling physical inequality is

```math
primeMass >= m_epsilon B_X - E_T - E_L - E_2 - E_M.
```

There is no factor `3` multiplying the four separate errors in this formulation.

Since `E_2` and `E_M` are now controlled asymptotically, the unresolved asymptotic FCL work is the source-exact derivation of `E_T` and `E_L` from the banked analytic owners.

## Correct Ford source architecture — two raw lanes

A hostile source audit superseded the old single-master-index picture.

```text
I_raw = I_Tot disjoint_union I_U.
```

- `I_Tot` reconstructs the full `T_X` correlation and is sourced through Ford–Maynard Lemma 7.21 / Type-I machinery.
- `I_U` reconstructs the leakage `L_X`; Proposition 7.22 is the `U`-lane expansion and is the lane carrying Type-II subproduct bookkeeping.

Only the `U` lane carries the nonempty selected-subproduct family `mathcal E` and a deterministic distinguished `E_*(mathcal E)`. Selected-E data must not be fabricated on the `Tot` lane.

Continuous Perron/Mellin ordinates remain bound integration variables inside finitely indexed contour packets rather than becoming elements of a finite discrete source index.

## Correct owner typing — one copy versus two copies

`C0`, `Transverse`, and `bDiagonal` are two-copy dispersion classifications. They depend on variables such as

```math
Delta=t1*n2-t2*n1
```

and on the relation between `b1` and `b2`; they therefore cannot be unique owners of a one-copy physical source row.

The correct hierarchy is

```text
one-copy raw packet
  -> Owner1 in {LowQ, Pascadi, Local}, when source-legitimate
  -> otherwise source-exact Cauchy/dispersion
  -> two-copy descendant
  -> shared-gcd formation
  -> proof-local Omega_H partition
  -> Owner2 in {C0, Transverse, bDiagonal, Local}.
```

The proof-local shared-gcd coordinate is introduced only after two copies exist.

## Running master-source refinement

The currently running source audit has exposed a further typing obstruction in the previous compiler target: the `Tot` lane actually follows Lemma 7.21 / Type-I, while the three dispersion owners cover a specific K0 smooth-parent two-copy normal form. The run is now locating the first literal coefficient-dictionary mismatch.

This is **not** a retraction of the banked C0/transverse/`b`-diagonal estimates. It means the previous demand that every hard raw packet enter one common two-copy normal form was too strong.

The controlling compiler target remains, in corrected two-lane form,

```text
FORD-Hepsilon-TWOLANE-RAWPACKET-TO-TWOCOPY-TYPEDOWNER-REFINEMENT45
```

with the proviso that only source-legitimate hard descendants are sent into the two-copy dispersion owner tree.

## Downstream status

```text
physical N2 Lambda collar        CLOSED asymptotically
Bsrc / N1 / E_M                  CLOSED asymptotically
four-error transference          CLOSED
FCL -> WindowPair, M>=12         CLOSED mathematically
E_T / E_L source compilation     OPEN
asymptotic FCL                   OPEN pending E_T/E_L
explicit threshold / finite splice OPEN
Erdos287ClosureInputs            UNINHABITED
Erdos287Statement                OPEN
```

## Effectivity / explicit-threshold firewall

The final formal splice requires an explicit `M0` with

```text
M0 <= 4,000,000,000
```

and eventual `WindowPairSupply` for all `M >= M0`. This is a last-mile explicit-constant problem, not another Type-II theorem. It should be finalized only after the asymptotic FCL source compiler is closed.

## Current dependency chain

```text
Tot lane -> Lemma 7.21 / Type-I dictionary
                 \
                  > exact E_T/E_L source compiler
                 /
U lane -> Proposition 7.22 / selected-E hard packets
       -> source-legitimate two-copy descendants
       -> C0 / Transverse / bDiagonal / Local

N2 collar CLOSED + Bsrc/N1/E_M CLOSED
                 |
                 v
          asymptotic FCL
                 |
                 v
WindowPairSupply (already closed from FCL, M>=12)
                 |
                 v
explicit threshold / finite splice
                 |
                 v
Erdos287Statement
```

## Erdős #287

**OPEN.** No unconditional large-`M` theorem, no explicit final `M0`, and no `Erdos287ClosureInputs` inhabitant are claimed.
