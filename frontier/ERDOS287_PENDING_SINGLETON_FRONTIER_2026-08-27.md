# Erdős #287 — pending singleton provider frontier

**Date:** 27 August 2026  
**Status:** research frontier only; Erdős #287 remains open.

## New structural reduction

The current smooth-parity branch has been reduced from a many-factor/depth-bounded Type-II packet to a **canonical singleton**.

Let
\[
\sigma=\nu_0-2\varepsilon_*,\qquad \nu_0=0.16623.
\]
For the literal `k=0` smooth-leakage branch, Ford–Maynard splittability and fragmentation give
\[
u=u_1\cdots u_s,\qquad v=v_1\cdots v_r,\qquad s,r\le20,
\]
hence at most forty 1-bounded factors. However the selected Type-II factor need not be a depth-5 subproduct: one may canonically choose a single nonterminal chunk
\[
m=
\begin{cases}
u_1,&s\ge2,\\
v_1,&s=1,\ r\ge2,
\end{cases}
\]
with
\[
X^{\sigma/3}<m\le X^\sigma.
\]
For sufficiently small fixed \(\varepsilon_*\),
\[
(X/2)^{\varepsilon_*}<m<X^{1/6},
\]
so this singleton lies wholly inside the relevant Type-II scale.

The resulting generated packet has the literal form
\[
\sum_{mn\asymp X}
\xi(m)\kappa(n)W(mn/X)
\bigl[\Lambda(2mn-1)+\Lambda(2mn+1)-4B(mn)\bigr],
\]
where
\[
X^{\sigma/3}<m\le X^\sigma,\qquad |\xi(m)|\le1,
\]
and \(\kappa\) is the convolution of at most 39 actual 1-bounded generated factors.

Two source-faithful singleton branches occur:

- **Möbius singleton:** \(\xi(m)=\mu(m)\) times box/Mellin/order-separation factors;
- **model singleton:** \(\xi(m)=m^{it}\) times box/Mellin/order-separation factors.

In the model-singleton branch the original short Möbius carrier remains in the complement grammar.

## Current first analytic open

The controlling singleton theorem is

`287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45`.

A sufficient target is
\[
\sum_{mn\asymp X}
\xi(m)\kappa(n)W(mn/X)
\bigl[\Lambda(2mn-1)+\Lambda(2mn+1)-4B(mn)\bigr]
=o(X/\log X)
\]
uniformly for the **actual generated singleton/complement pairs**, not for arbitrary divisor-bounded coefficients.

The older depth-5 target is retired as controlling.

## Next provider audit

The next research run should be

`SINGLETON-TO-GATE1B-LITERAL-PROVIDER-DICTIONARY45`.

It should preserve the literal complement grammar
\[
\kappa=\eta_1*\cdots*\eta_r,\qquad r\le39,
\]
with each factor labelled by:

- Möbius/model/Mellin/cutoff type;
- support exponent;
- terminal/nonterminal status;
- squarefree/coprimality data;
- coefficient norm.

Then split the affine signs \(2mn\pm1\), perform exactly one source-exact completion, and test only:

1. Möbius singleton -> Gate-1B signed/common-conductor lane;
2. model singleton -> QK56/direct affine lane, retaining the complement Möbius carrier;
3. Gate 1A only if a literal common-weight physical packet appears;
4. otherwise print the first exact new residual theorem with ranges, norms, sign, prefactor and required saving.

No match may be declared merely because two formulae contain a Möbius factor.

## Current ledger

| Node | Status |
|---|---|
| exact `k=0` smooth leakage source | PASS |
| Möbius splittability | PASS |
| fragmentation `s,r<=20`, total depth `<=40` | PASS |
| canonical singleton `E={m}` | PASS |
| depth-5 target | RETIRED AS CONTROLLING |
| singleton generated Type II | **FIRST ANALYTIC OPEN** |
| literal singleton -> Gate-1B/1A/direct provider dictionary | **NEXT** |
| singleton cancellation | OPEN |
| remaining fixed-`g_*` packet census | OPEN |
| fixed-certificate leakage | OPEN |
| Erdős #287 | OPEN |

## Firewall

This update is a research reduction, not a theorem that the singleton estimate holds. Existing universal/generated Ford–Maynard routes remain valid sufficient alternatives. The repository's trusted finite Lean result is unchanged.
