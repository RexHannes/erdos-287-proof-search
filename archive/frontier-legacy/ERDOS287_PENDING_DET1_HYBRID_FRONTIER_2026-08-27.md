# Erdős #287 — determinant-one hybrid frontier

**Date:** 27 August 2026  
**Status:** research frontier only. Erdős #287 remains open.

This note supersedes the earlier *next-action* claim in `ERDOS287_PENDING_SINGLETON_FRONTIER_2026-08-27.md`. The singleton reduction remains useful, but its literal provider dictionary has now been audited.

## 1. Provider dictionary verdict

The canonical singleton packet is **not** literally the existing Gate-1B common-conductor signed covariance.

For a fixed affine sign
\[
s\in\{-1,+1\},\qquad L_s=2mn+s,
\]
one has the exact coprimality identities
\[
(m,L_s)=(m,s)=1,\qquad (n,L_s)=(n,s)=1.
\]
Hence every nontrivial divisor of the Ford outer variables `m` or `n` is coprime to the shifted output `L_s`.

This gives the source-provenance no-go

```text
FORD-OUTER-MU != GATE1B-HICOND-COMPLEMENT-MU.
```

The Möbius factor `mu(m)` in the Ford singleton is an **outer Type-II coefficient**. The Gate-1B high-conductor Möbius factor arises later from a factor of the shifted-output modulus. They are different variables and may not be identified merely because both carry a Möbius sign.

Current verdict:

```text
SINGLETON-TO-GATE1B-DIRECT-DICTIONARY45: FAIL
OUTER-vs-SHIFTED-MOBIUS-CARRIER-NOGO45: PASS
```

Gate 1B is still relevant only after the shifted output `2mn+s` is decomposed. A future Gate-1B theorem would have to be stable under the actual generated outer coefficients `xi(m), kappa(n)`.

## 2. Short depth-2 selection

The earlier canonical singleton `E={m}` is structurally simplest, but a stronger provider-matching selection is available.

Let
\[
\sigma=\nu_0-2\varepsilon_*,\qquad \nu_0=0.16623.
\]
After Ford fragmentation, each nonterminal exponent lies in `(sigma/3,sigma]`, with at most two terminal exponents in `[0,sigma/3]`. Set
\[
\rho=\frac3{20}.
\]
Then one can select a subproduct `E` with
\[
\boxed{1\le |E|\le2,\qquad X^{\varepsilon_*}<m_E\le X^{3/20+o(1)}.}
\]

Research verdict:

```text
287-SHORT-DEPTH2-TYPEII-SELECTION45: PASS
```

This retires depth-5 as a controlling structural target.

## 3. Wright-compatible subrange

The selected depth-`<=2` short coefficient lies below the numerical exponent `3/20`, which is below the short-factor exponent appearing in Wright's unbalanced AP theorem. This yields a **conditional subrange provider only**, provided the actual generated coefficient satisfies the required uniform Siegel-Walfisz condition and the progression-discrepancy dictionary is literal.

```text
SHORT-DEPTH2-WRIGHT-AP-ADAPTER45: CONDITIONAL SUBRANGE PASS
```

It is not a proof of the full affine singleton correlation.

## 4. Multiouter algebraic reduction

Any shifted-output source with finitely many outer convolution factors can be partitioned into two generated outer blocks by exact associativity of Dirichlet convolution:
\[
\Delta_{\psi_1,\ldots,\psi_t}(r)
=
\sum_{ab=r}\Psi_I(a)\Psi_J(b).
\]
Thus separate 3-outer and 4-outer *algebraic* source theorems are no longer independent blockers.

```text
MULTIOUTER-TO-GENERATED-TWOOUTER45: PASS
```

The resulting generated two-outer **analytic estimate** remains open.

## 5. Current first general analytic open

After removing:

- large shifted-output blocks already routable through the existing one-outer/F3 mechanism;
- Wright-compatible low/moderate-modulus AP children, subject to their source adapter;
- principal, zero and nonunit pieces;
- native-QK children when a literal QK5 adapter and outer-coefficient stability certificate exist;

one obtains the determinant-one two-outer residual
\[
\boxed{
\mathcal K^{(2)}_{s,\pi}
=
\sum_{q\sim Q}\lambda_\pi(q)
\sum_{\substack{m\sim M,\ n\sim N\\ qab=2mn+s}}
\xi_\pi(m)\kappa_\pi(n)
\Psi_{\pi,1}(a)\Psi_{\pi,2}(b),
}
\]
with
\[
MN\asymp X,\qquad M=X^\mu,\qquad \varepsilon_*<\mu\le\frac3{20},\qquad QAB\asymp X.
\]

Since
\[
(qa)b-(2m)n=s=\pm1,
\]
one has
\[
(qa,2m)=1,\qquad (b,n)=1.
\]
Fixing `q,a,m` and one particular solution gives the exact affine parametrisation
\[
\boxed{b=b_0+2mt,\qquad n=n_0+qa\,t.}
\]
Therefore the remaining kernel is the literal hybrid affine correlation
\[
\sum_{q,a,m}
\lambda_\pi(q)\Psi_{\pi,1}(a)\xi_\pi(m)
\sum_{t\in I_{q,a,m}}
\Psi_{\pi,2}(b_0+2mt)\,
\kappa_\pi(n_0+qa\,t),
\]
together with the corresponding principal/main-term subtraction.

Programme label:

```text
AFFINE287-DET1-HYBRID-MQ45
```

Equivalent Gate-1B-style label:

```text
HYBRID-MQ-KLOOSTERMAN-LARGE-SIEVE
```

**This is the current first general analytic open exposed by the provider audit.**

No currently cited theorem is being claimed to control this full generated `q,a,m` family with its affine sign, common/composite conductors, outer coefficient grammar, Möbius coherence and conductor reassembly.

## 6. Where common-conductor covariance fits

The existing common-conductor signed covariance is a possible **high-conductor child** of the singleton-generated problem, not the singleton problem itself.

To route a packet there still requires both:

```text
SINGLETON-TO-NATIVE-QK5-SOURCE-ADAPTER45
OUTER-GENERATED-COEFFICIENT-STABILITY-OF-CC45
```

Neither is presently recorded as proved.

Thus the correct relation is

```text
common-conductor signed covariance
    subset of possible high-conductor children of singleton-generated Type II,
```

not equality.

## 7. Current closure-minimising DAG

```text
k=0 smooth leakage                         PASS
        |
        v
Ford fragmentation                         PASS
        |
        v
short selection |E|<=2, m_E<=X^(3/20)      PASS
        |
        +--> large shifted-output block --> routable one-outer/F3 sector
        +--> Wright-compatible AP child --> conditional subrange provider
        +--> native QK5 child -----------> CC covariance + outer stability
        +--> other multiouter -----------> generated two-outer
        |
        v
AFFINE287-DET1-HYBRID-MQ45                 OPEN
        |
        v
k=0 smooth-parity closure                   OPEN
        |
        v
remaining fixed-g* packets                  OPEN
        |
        v
FCL                                         OPEN
        |
        v
positive affine prime mass
        |
        v
WindowPairSupply / Sophie witness
        |
        v
trusted finite Lean compiler
        |
        v
Erdős #287                                  OPEN
```

## 8. Exact ledger

| Node | Current research verdict |
|---|---|
| singleton outer coefficient classes | source-exact PASS |
| every branch has a useful Möbius carrier | FALSE |
| Ford outer `mu(m)` = Gate-1B shifted complement `mu(r)` | FALSE by coprimality |
| direct singleton -> common-conductor dictionary | FAIL |
| selected Type-II depth `<=2`, exponent `<=3/20` | PASS |
| Wright AP child | conditional subrange PASS |
| 3-/4-outer algebraic census | reduced to generated two-outer |
| one-outer Gate-1B sector | conditional existing provider |
| common-conductor signed covariance | open high-conductor child / provider candidate |
| `AFFINE287-DET1-HYBRID-MQ45` | **FIRST GENERAL ANALYTIC OPEN** |
| `k=0` smooth packet | OPEN |
| FCL | OPEN |
| Erdős #287 | OPEN |

## Firewall

This file records a research audit and source-routing reduction. `PASS` means the stated finite/algebraic/research reduction is being banked at the research level described here; it does not promote an analytic result into Lean or into a published theorem. The trusted finite Lean result is unchanged.