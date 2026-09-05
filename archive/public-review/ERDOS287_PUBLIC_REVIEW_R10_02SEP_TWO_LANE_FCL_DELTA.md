# Erdős Problem #287 — Public Review R10 Delta

**Date:** 2 September 2026  
**Status:** research / closure-candidate update.  
**Public verdict:** **ERDŐS PROBLEM #287 REMAINS OPEN.**

This R10 delta supersedes the immediate R9 source/compiler frontier while preserving R9 and all earlier drafts as historical provenance. It records the latest source-exact hostile audits. It does **not** claim that the new paper/research analytic results are Lean-certified, and it does **not** claim an unconditional solution of Erdős #287.

## 1. Strongest unconditional theorem

The existing machine-checked finite theorem excluding exact counterexamples with maximum denominator

```text
M <= 4,000,000,000
```

is unchanged.

The large-`M` endgame remains conditional on an asymptotic fixed-certificate lower bound and, finally, an explicit threshold/finite splice.

## 2. Paper/research results now banked

The following are closed at the paper/research level under the source dictionaries stated in their audit reports:

```text
287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45
287-K0-SP2-UNIFORM-FRAGMENTATION-REASSEMBLY45
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45        [for already-typed local packets]
GLOBAL-BSRC-COMPARISON-MARGIN45            [asymptotic]
N1-BSRC-DICTIONARY                         [asymptotic]
E_M = o(B_X)                               [asymptotic]
FIXEDCERTIFICATE-N2-LAMBDA-COLLAR45        [fixed-epsilon asymptotic]
FOUR-ERROR FIXED-CERTIFICATE TRANSFERENCE
FCL_W(M/2) -> WindowPairSupply(M), M >= 12
```

These are not all Lean analytic theorems. Where the public formal tree contains only an explicit input/interface, the paper-level result remains classified as an external analytic bank rather than being promoted by fiat.

## 3. Physical N2 Lambda collar — closed asymptotically

For the literal physical sequence

```math
w_X(n)=W(n/X)[\Lambda(2n-1)+\Lambda(2n+1)-4B_{\rm src}(n)],
```

the old bounded-sequence `N_2` estimate is **not** used. Instead the source-specific argument proves:

1. if `H_epsilon(n) != 0` on `N_2`, then `n` is `sigma`-rough;
2. `Omega(n) <= 6` and `|H_epsilon(n)| <= 64`;
3. squareful `n` and proper shifted prime powers are negligible;
4. on the squarefree source, write `n=Mq` with `q` the largest prime factor;
5. the two linear forms are `q` and `2Mq+s`;
6. their singular series is exactly
   ```math
   \mathfrak S(M,s)=2B_{\rm src}(M),
   ```
   independently of `s`;
7. a dimension-two Selberg upper sieve supplies the correct `1/log X` Lambda-weighted upper bound;
8. the Ford five-collar geometry has logarithmic volume `O(epsilon)`.

Thus

```math
\frac{E_2}{B_X}\le K_{\rm collar}\,\varepsilon+o(1).
```

For one fixed sufficiently small `epsilon`, eventually

```math
E_2 \le \frac{m_\varepsilon}{8} B_X.
```

This proves `FIXEDCERTIFICATE-N2-LAMBDA-COLLAR45` at the asymptotic fixed-`epsilon` mathematical level. No explicit numerical `epsilon`, `K_collar`, or large-`X` threshold is claimed yet.

## 4. Bsrc / N1 comparison — closed asymptotically

The physical comparison is fixed as

```math
B_{\rm src}(n)=\mathfrak S_2\prod_{p\mid n,\,p>2}\frac{p-1}{p-2},
```

and

```math
b_X(n)=4W(n/X)B_{\rm src}(n).
```

The latest source audit proves the generalized-PNT dictionary required on `N_1`, giving

```math
E_M=o(B_X),
```

and

```math
B_X=\left(4\mathfrak S_2\int W+o(1)\right)\frac{X}{\log X}.
```

The Ford limiting margin satisfies

```math
m_0\ge 6\times10^{-6},
```

and the support-truncated perturbed certificate has

```math
m_\varepsilon=m_0+O(\varepsilon)>0
```

for sufficiently small fixed `epsilon`. No explicit perturbation constant is claimed in this version.

## 5. Exact four-error FCL algebra

The correct physical transference inequality is

```math
\text{prime mass}
\ge
m_\varepsilon B_X-E_T-E_L-E_2-E_M.
```

There is no factor `3` multiplying the four errors in this formulation.

Because `E_2` and `E_M` are now controlled asymptotically, the current asymptotic FCL frontier is the exact source binding required to obtain `E_T` and `E_L` from the banked analytic owners.

## 6. Mandatory two-lane Ford source architecture

A hostile source audit corrected an over-strong master-index formulation.

The raw physical source has two different lanes:

```text
I_raw = I_Tot disjoint_union I_U.
```

- `I_Tot` reconstructs the full correlation `T_X` and follows the Ford–Maynard Lemma 7.21 / Type-I route.
- `I_U` reconstructs the leakage correlation `L_X`; Proposition 7.22 is the `U`-lane expansion and is the lane carrying the Type-II subproduct bookkeeping.

Therefore Proposition 7.22 must **not** be treated as an expansion of the full `T_X` lane.

### 6.1 Selected-E bookkeeping

The `U` lane first carries a nonempty collection

```math
\varnothing\ne\mathcal E\subseteq\mathcal P([N])\setminus\{\varnothing\}.
```

The source coefficient retains the inclusion-exclusion factor depending on the whole `mathcal E`. A deterministic distinguished subset

```math
E_*(\mathcal E)=\min_{\prec}\mathcal E
```

is then used as the Type-II grouping coordinate. Retaining only one `E` and its complement would lose the original inclusion-exclusion data; summing the same row independently over every possible distinguished `E` would duplicate it.

Selected-`E` data is absent on the `Tot` lane.

### 6.2 Perron ordinates

The discrete raw source index is finite, but continuous Perron/Mellin ordinates remain bound integration variables inside each contour packet. They are not fabricated as elements of a finite discrete index.

## 7. Mandatory one-copy / two-copy owner separation

Another hostile audit corrected an over-strong owner function.

`C0`, `Transverse`, and `b`-Diagonal depend on two-copy dispersion coordinates such as

```math
\Delta=t_1n_2-t_2n_1
```

and on the relation between `b_1` and `b_2`. Consequently they cannot be unique owners of a one-copy physical packet.

The correct typing is:

```text
one-copy raw packet
  -> one-copy easy owner (LowQ / Pascadi / Local), if applicable
  -> otherwise exact Cauchy/dispersion
  -> two-copy descendant
  -> shared-gcd formation
  -> proof-local Omega_H partition
  -> Owner^(2) in {C0, Transverse, bDiagonal, Local}.
```

The shared-gcd `Omega_H` coordinate is introduced only after two copies exist.

## 8. New refinement from the running master-source audit

The current running hostile audit has identified a further typing point: the `Tot` lane should not be forced through the K0 smooth-parent dispersion owners merely because those owners are available. The `Tot` lane is sourced through Lemma 7.21 / Type-I, while the hard `U` lane is the natural place for Proposition-7.22 Type-II descendants and subsequent two-copy dispersion.

This observation is presently a **compiler refinement under audit**, not yet a promoted theorem. The exact first coefficient dictionary mismatch is still being located. It does not retract the already-banked local analytic estimates.

Accordingly the controlling source/compiler target is retained in corrected form as

```text
FORD-Hepsilon-TWOLANE-RAWPACKET-TO-TWOCOPY-TYPEDOWNER-REFINEMENT45
```

with the explicit proviso that only source-legitimate hard descendants are sent into the two-copy owner tree.

## 9. Current asymptotic dependency chain

```text
Tot lane -> Lemma 7.21 / Type-I source dictionary
                 \
                  > exact E_T / E_L source compiler
                 /
U lane -> Proposition 7.22 -> selected-E hard packets
       -> source-legitimate two-copy descendants
       -> C0 / Transverse / bDiagonal / Local owners

N2 Lambda collar                    [CLOSED asymptotically]
Bsrc / N1 / E_M                     [CLOSED asymptotically]
positive Ford margin                [PASS asymptotically]
                 |
                 v
          asymptotic FCL
                 |
                 v
FCL -> WindowPairSupply, M>=12       [CLOSED]
                 |
                 v
explicit threshold / finite splice   [OPEN]
                 |
                 v
Erdos287Statement                    [OPEN]
```

## 10. Effectivity / explicit-threshold splice

Effectivity is a separate last-mile issue, not another Type-II theorem. After asymptotic FCL is source-exactly closed, the project must extract explicit constants/thresholds for the Ford perturbation, collar estimate, comparison mass, and aggregate owner bounds.

The formal endgame currently requires an explicit `M_0` satisfying

```text
M_0 <= 4,000,000,000
```

and

```text
forall M >= M_0, WindowPairSupply(M).
```

If a first explicit analytic threshold exceeds the finite certified range, the alternatives are to sharpen the analytic constants or extend the finite verification. No numerical `M_0` is claimed here.

## 11. Formal / Aristotle status

The append-only formal programme is intentionally conservative. New paper/research results such as the physical N2 Lambda collar and the Bsrc/N1 asymptotic comparison should be recorded as `paperClosedExternal` until a genuine Lean analytic proof exists. The raw/two-copy source compiler and effectivity inputs remain uninhabited.

No `Erdos287ClosureInputs` inhabitant and no unconditional `Erdos287Statement` proof are claimed.

## 12. Current verdict

**Erdős Problem #287 remains OPEN.**

The principal asymptotic research bottleneck is no longer `N_2`, `Bsrc/N1`, the four-error FCL algebra, or the FCL-to-WindowPair dictionary. It is the exact two-lane source/compiler construction that connects the physical Ford `H_epsilon` correlations to their source-legitimate analytic owners. The running source audit may further reduce this by routing the `Tot` lane directly through its Lemma-7.21 Type-I owner rather than through the two-copy dispersion tree.

After asymptotic FCL, the remaining last mile is explicit-threshold compilation and the finite/asymptotic splice.
