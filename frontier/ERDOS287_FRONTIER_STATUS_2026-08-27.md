# Erdős Problem #287 — Research Frontier (27 Aug 2026)

**Status: OPEN problem / research frontier. This repository does not claim a proof of Erdős #287 or twin-prime infinitude.**

## Formal layer remains unchanged

The trusted Lean project still supplies the finite Erdős-287 reduction and finite verification only. Nothing in this research frontier is promoted into Lean merely by appearing here.

## Fixed-certificate route

The explicit fixed Ford certificate and fixed-certificate transference remain valid research-level reductions. The fixed-certificate leakage census is not exhausted by H8/H9; the literal `k=0` branch contains a smooth truncated-Möbius parity packet.

A later fragmentation audit now gives a stronger structural reduction of that packet.

## New singleton reduction

Set

```text
sigma = nu0 - 2 epsilon*,   nu0 = 0.16623.
```

Ford–Maynard splittability/fragmentation yields smooth-factor decompositions with

```text
s,r <= 20,   total generated depth <= 40.
```

However the Type-II factor can be chosen canonically as one nonterminal chunk:

```text
E = {m},   |E| = 1,
X^(sigma/3) < m <= X^sigma.
```

For sufficiently small fixed `epsilon*`,

```text
(X/2)^epsilon* < m < X^(1/6).
```

Thus the old depth-5 selected-subproduct target is retired as controlling.

The resulting singleton packet is

```text
sum_{mn~X} xi(m) kappa(n) W(mn/X)
  [Lambda(2mn-1)+Lambda(2mn+1)-4B(mn)],
```

where `xi` is one actual generated singleton factor and `kappa` retains the convolution grammar of at most 39 actual 1-bounded factors.

Two source-faithful singleton branches are distinguished:

- Möbius singleton: `xi(m) = mu(m) * box/Mellin/order factors`;
- model singleton: `xi(m) = m^(it) * box/Mellin/order factors`, with the Möbius carrier remaining in the complement grammar.

## First analytic open

The new controlling theorem is

`287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45`.

A sufficient target is `o(X/log X)` uniformly over the **actual generated singleton/complement pairs**. It is not necessary, and would be stronger, to replace the complement by arbitrary `tau_39` coefficients.

Current provider status: no direct published black box has been certified for this exact source class.

## Next run

The next research action is

`SINGLETON-TO-GATE1B-LITERAL-PROVIDER-DICTIONARY45`.

The provider dictionary must preserve every complement factor with its:

- Möbius/model/Mellin/cutoff type;
- support exponent;
- terminal/nonterminal status;
- squarefree/coprimality condition;
- coefficient norm.

Then split the affine signs `2mn+1` and `2mn-1`, perform one literal source completion, and allow only four outcomes:

1. Möbius singleton -> Gate-1B signed/common-conductor source;
2. model singleton -> QK56/direct affine source, retaining the complement Möbius carrier;
3. Gate 1A only upon a literal common-weight physical match;
4. otherwise state the first exact new residual theorem with ranges, norms, sign, prefactor and required saving.

Structural resemblance alone is not a provider dictionary.

## Current distance ledger

| Node | Status |
|---|---|
| explicit fixed certificate | PASS |
| fixed-certificate transference | PASS |
| exact `k=0` smooth leakage source | PASS |
| Möbius splittability | PASS |
| fragmentation `s,r<=20`, depth `<=40` | PASS |
| canonical singleton `E={m}` | PASS |
| depth-5 target | RETIRED AS CONTROLLING |
| singleton generated Type II | **FIRST ANALYTIC OPEN** |
| singleton -> Gate-1B/1A/direct literal provider dictionary | **NEXT** |
| singleton cancellation | OPEN |
| remaining fixed-`g_*` packet census | OPEN |
| fixed-certificate leakage | OPEN |
| Ford lower-bound completion | CONDITIONAL/OPEN |
| Erdős #287 | OPEN |

## Research firewall

The universal Ford–Maynard Type-II route and the generated-(7.23) route remain valid sufficient alternatives. The singleton reduction solves structural routing for the first smooth-parity packet; it does **not** prove the analytic cancellation. Gate 1A and Gate 1B remain providers only when a literal source dictionary is proved.
