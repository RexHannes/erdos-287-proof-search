# Erdős Problem #287 — Research Frontier (27 Aug 2026)

**Status: OPEN problem / research frontier. This repository does not claim a proof of Erdős #287 or twin-prime infinitude.**

## Formal layer remains unchanged

The trusted Lean project still supplies the finite Erdős-287 reduction and finite verification only. Nothing in this research frontier is promoted into Lean merely by appearing here.

## Fixed-certificate / smooth-parity route

The explicit fixed Ford certificate and fixed-certificate transference remain valid research-level reductions. The literal `k=0` smooth-parity packet is source-exact, and Ford fragmentation has removed the earlier many-variable structural ambiguity.

A previous audit reduced the selected Type-II factor to a canonical singleton. The latest provider audit goes further: it proves that the singleton is **not literally the existing Gate-1B common-conductor signed covariance**, and it isolates a narrower determinant-one hybrid residual.

## Provider-dictionary correction

For a fixed sign

```text
s in {-1,+1},   L_s = 2mn+s,
```

one has the exact coprimality identities

```text
(m,L_s)=1,   (n,L_s)=1.
```

Therefore Ford outer Möbius factors attached to divisors of `m` or `n` are not the shifted-output modulus Möbius factors arising inside the Gate-1B high-conductor decomposition.

Current verdict:

```text
SINGLETON-TO-GATE1B-DIRECT-DICTIONARY45: FAIL
OUTER-vs-SHIFTED-MOBIUS-CARRIER-NOGO45: PASS
```

Gate 1B remains a possible provider only after a literal shifted-output decomposition and a theorem stable under the actual generated outer coefficients.

## Stronger short selection

The canonical singleton remains valid, but for provider matching the generated short coefficient can be selected with

```text
1 <= |E| <= 2,
X^epsilon* < m_E <= X^(3/20+o(1)).
```

Research verdict:

```text
287-SHORT-DEPTH2-TYPEII-SELECTION45: PASS
```

The older depth-5 target remains retired as controlling.

## Routed / conditional subranges

The current audit separates several children before the first general residual:

- large shifted-output block -> existing one-outer/F3 route;
- low/moderate-modulus AP child -> Wright-compatible route, conditional on the generated short coefficient satisfying the required Siegel-Walfisz adapter;
- native QK5 child -> possible common-conductor covariance child, conditional on a literal QK5 source adapter and outer-generated-coefficient stability;
- 3-/4-/higher-outer algebraic sources -> exact reduction to generated two-outer by Dirichlet-convolution associativity.

The last item is recorded as

```text
MULTIOUTER-TO-GENERATED-TWOOUTER45: PASS.
```

The resulting generated two-outer analytic estimate is not thereby proved.

## Current first general analytic open

After the routed sectors above, the exact residual can be written

\[
\mathcal K^{(2)}_{s,\pi}
=
\sum_{q\sim Q}\lambda_\pi(q)
\sum_{\substack{m\sim M,\ n\sim N\\qab=2mn+s}}
\xi_\pi(m)\kappa_\pi(n)
\Psi_{\pi,1}(a)\Psi_{\pi,2}(b),
\]

with

```text
MN ~ X,
M = X^mu,
epsilon* < mu <= 3/20,
QAB ~ X.
```

Since

```text
(qa)b - (2m)n = s = +/-1,
```

one has

```text
(qa,2m)=1,   (b,n)=1,
```

and after fixing `q,a,m` and one particular solution,

```text
b = b0 + 2m t,
n = n0 + qa t.
```

Thus the remaining problem is the coherent hybrid affine correlation

```text
sum_{q,a,m} lambda(q) Psi1(a) xi(m)
  sum_{t in I(q,a,m)} Psi2(b0+2mt) kappa(n0+qa t),
```

with the actual generated source selectors and main-term subtraction retained.

Programme label:

`AFFINE287-DET1-HYBRID-MQ45`.

Equivalent descriptive label:

`HYBRID-MQ-KLOOSTERMAN-LARGE-SIEVE`.

This is now the **FIRST GENERAL ANALYTIC OPEN** in the `k=0` smooth-parity route.

## Where common-conductor covariance sits

The existing common-conductor signed covariance is only a possible high-conductor child of the singleton/generated problem. Routing a packet there still requires

```text
SINGLETON-TO-NATIVE-QK5-SOURCE-ADAPTER45
OUTER-GENERATED-COEFFICIENT-STABILITY-OF-CC45.
```

Therefore the correct relation is

```text
common-conductor signed covariance
  subset of possible high-conductor children of the singleton-generated problem,
```

not equality.

## Current distance ledger

| Node | Status |
|---|---|
| explicit fixed certificate | PASS |
| fixed-certificate transference | PASS |
| exact `k=0` smooth leakage source | PASS |
| Ford fragmentation / splittability | PASS |
| canonical singleton | PASS |
| direct singleton -> Gate-1B common-conductor dictionary | FAIL |
| Ford outer Möbius = shifted-output Möbius | FALSE by exact coprimality |
| short selection `|E|<=2`, exponent `<=3/20` | PASS |
| Wright AP child | CONDITIONAL SUBRANGE PASS |
| multiouter -> generated two-outer | PASS algebraically |
| one-outer Gate-1B sector | conditional existing provider |
| common-conductor covariance | possible open high-conductor child |
| `AFFINE287-DET1-HYBRID-MQ45` | **FIRST GENERAL ANALYTIC OPEN** |
| `k=0` smooth-parity closure | OPEN |
| remaining fixed-`g_*` packet census | OPEN |
| fixed-certificate leakage | OPEN |
| Ford lower-bound completion | CONDITIONAL/OPEN |
| Erdős #287 | OPEN |

## Current next run

See [`ERDOS287_NEXT_AFFINE287_DET1_HYBRID_MQ45.md`](ERDOS287_NEXT_AFFINE287_DET1_HYBRID_MQ45.md).

The next attack should work on the exact determinant-one hybrid source, preserving the affine sign, generated outer coefficient grammar, prefactor, conductor data, Möbius provenance, norms, multiplicities and all exceptional strata. It should either close the hybrid estimate, specialize it literally to an existing theorem, or print a strictly narrower residual.

## Research firewall

The universal Ford–Maynard Type-II route and generated-(7.23) route remain valid sufficient alternatives. The structural reductions above do **not** prove the determinant-one hybrid cancellation, `k=0` smooth-parity closure, FCL, the large-`M` supply, or Erdős #287. Gate 1A and Gate 1B are providers only when literal source dictionaries and stability hypotheses are proved.