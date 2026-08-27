# Erdős #287 — Aristotle V13 update

**Status: open problem / safe formal update.  This file does not claim a solution of Erdős #287.**

This update records the post-V12/V13 research frontier without promoting any analytic
claim into the trusted Lean bank.

## 1. Finite formal layer

The existing project remains the controlling formal result:

- exact public counterexample predicate;
- top-layer p-adic obstruction and adjacent-hole compiler;
- exact `WindowPairSupply` interface;
- kernel-checked exclusion of every exact counterexample with
  `3 ≤ M ≤ 4,000,000,000`;
- no `sorry`, `admit`, project axiom, `unsafe`, or `native_decide` is required by the
  finite chain.

`WindowPairSupply` is still the exact formal large-`M` input.  It already includes
`M ≤ 2*x`, so the two consecutive forced holes lie in the upper half after using the
banked half-range placement theorem.

## 2. Repair of the older log-cofactor interface

The older exploratory `Challenges.Delta6.LCBeta` did not contain the upper-half
placement `M ≤ 2*x`.  It therefore does not literally feed the finite adjacent-hole
blocker by itself.

`RequestProject/Status/Erdos287V13Frontier.lean` now records the corrected OPEN
interface

```lean
Erdos287.LCBetaUpperHalf M J
```

which adds that placement condition.  No theorem asserts that it holds for all large
`M`.

A paper-level asymptotic observation remains useful: if

\[
J(M)\asymp \eta\frac{\log M}{\log\log M},\qquad 0<\eta<\frac12,
\]

and a prime satisfies `M ≤ 2 J(M) q`, then the already-proved bound
`C(j) ≤ j·j!` implies, for sufficiently large `M`, both `q^2 > M` and
`q > C(2J(M))`.  Thus the genuinely difficult part is the *adjacent large-prime-factor
supply*, not the numerator bound.  This asymptotic step is not yet formalised in Lean.

## 3. Analytic frontier after V13

The post-V13 proof search suggests a narrower route than universal Ford–Maynard Type II:
control one fixed Ford certificate's leakage correlation directly.  Schematically the
research target is

\[
\sum_{n\in\mathcal U_{g_*}} H_{g_*}(n)W(n/X)
\bigl[\Lambda(2n-1)+\Lambda(2n+1)-4B(n)\bigr]
\ll_A X(\log X)^{-A}.
\]

This is **not** a theorem in the Lean project and is not imported by any proved result.
Likewise, the proposed affine Gate-1B H8/H9 source-to-Kummer splice and the proposed
quadratic-Kummer bilinear estimates remain analytic research items until their literal
source dictionaries, ranges, norms and estimates are independently verified.

Accordingly the safe status remains:

```text
FINITE ERDŐS-287 COMPILER: CLOSED
WINDOW-PAIR LARGE-M SUPPLY: OPEN
GATE 1A: OPTIONAL PROVIDER / CONDITIONAL
GATE 1B: OPEN ANALYTIC RESEARCH
FIXED-CERTIFICATE LEAKAGE ESTIMATE: OPEN
ERDŐS #287: OPEN
```

## 4. Gate 1A dependency correction

Gate 1A is **not logically mandatory** for the shortest #287 route.  It should be treated
only as a possible analytic provider.  It becomes relevant only if a literal #287
leakage/packet decomposition produces a packet matching Gate 1A's canonical
common-weight source and its scale dictionary.

Therefore no future #287 status ledger should contain

```text
FULL GATE 1A CLOSED
```

as an unconditional prerequisite.  The correct dependency is:

```text
use Gate 1A only for the actual packets that are source-exactly routed to it;
otherwise bypass it.
```

See `ERDOS287_GATE1A_V13_DRAFT_UPDATE.md` for publication-facing replacement text.
