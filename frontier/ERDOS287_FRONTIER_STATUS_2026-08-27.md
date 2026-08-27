# Erdős Problem #287 — Current Research Frontier (28 Aug 2026)

**Status: OPEN. This repository does not claim a proof of Erdős #287 or twin-prime infinitude.**

## Formal layer remains unchanged

The trusted Lean project still supplies the finite Erdős-287 reduction and finite verification only. Nothing in this research frontier is promoted into Lean merely by appearing here.

## Current two-front structure

The programme now has two distinct source-exact analytic fronts.

### M/Vaughan branch

The V14 affine-prime audit remains valid:

- `AFFINE287-VAUGHAN-PRIME-SOURCE45: PASS`;
- proper prime-power outer: PASS / negligible;
- literal Vaughan cofactor well-factorability: FALSE;
- direct Gate-1A canonical adapter: FAIL;
- direct native QK56 dictionary: not established;
- prime-modulus Möbius two-outer structural map: PASS.

The open theorem is

`AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`.

### Balanced-seven V-branch

The V15 balanced-seven audit reduces the equal seven-prime box at

```text
Q = X^(3/5),  Y = X^(1/7)
```

to a polarized smooth-multiplicative endpoint theorem.

The literal source is

\[
\mathcal B_{7,s}(X)
=
\sum_{q\sim X^{3/5}}\mu(q)
\left[
\sum_{\substack{p_1,\ldots,p_7\sim X^{1/7}\\
2p_1\cdots p_7\equiv-s\;(\bmod q)}}
\prod_{i=1}^{7}\omega_i(p_i)
-\mathfrak M_{7,s}(q)
\right].
\]

## Death tests

The following are now banked as nonclosing/no-go for this exact balanced-seven cell:

- ordinary separate multiplicative large sieve: `X^(1/10)` deficit;
- separated higher moments: same deficit;
- equal-seven P6.3 three-block dictionary: FALSE;
- termwise prime-box HB/P6.3 repair: nonexhaustive;
- q-Möbius micro-switch: nonexhaustive because the prime-q sector survives.

## Exact torus polarization

For `z=(z_1,...,z_7) in T^7`, define

\[
a_z(p)=\frac17\sum_{i=1}^{7}z_i\omega_i(p)
\]

on primes `p~Y`, and let `f_z` be the squarefree-supported multiplicative function with

\[
f_z(p)=a_z(p),\qquad f_z(p^\ell)=0\quad(\ell\ge2).
\]

For distinct primes,

\[
[z_1\cdots z_7]f_z(p_1\cdots p_7)
=
7^{-7}\sum_{\sigma\in S_7}\prod_{j=1}^{7}\omega_{\sigma(j)}(p_j).
\]

Thus the ordered labelled squarefree source is recovered exactly as a torus coefficient of a standard multiplicative progression sum.

Repeated-prime tuples contribute only

\[
O(X^{6/7+o(1)}).
\]

Moreover

\[
|\Lambda_{f_z}(p^\ell)|\le\Lambda(p^\ell),
\]

so the family lies uniformly in the standard smooth-supported multiplicative class.

Research verdicts:

```text
BALANCED7-SQUAREFREE-POLARIZATION45: PASS
BALANCED7-REPEATED-PRIME45: PASS
BALANCED7-SMOOTH-MULTIPLICATIVE-DICTIONARY45: PASS
```

## Exact polarized source identity

Let

\[
\Delta_{\rm LC}(f_z;X,q,a_s)
=
\sum_{\substack{n\asymp X\\n\equiv a_s\pmod q}}f_z(n)W(n/X)
-\mathcal E_q(f_z;a_s),
\]

where `E_q` is the principal + low-conductor expected term in the chosen beyond-1/2 convention.

Let `M^{pol}_{7,s}(q)` be the torus coefficient of this same expected term.

Then

\[
\begin{aligned}
\mathcal B_{7,s}(X)
={}&
7^7\int_{\mathbb T^7}\overline{z_1\cdots z_7}
\sum_{q\sim X^{3/5}}\mu(q)
\Delta_{\rm LC}(f_z;X,q,a_s)\,dz\\
&+
\sum_{q\sim Q}\mu(q)
\bigl(M^{pol}_{7,s}(q)-M_{7,s}(q)\bigr)
+O(X^{6/7+o(1)}).
\end{aligned}
\]

Therefore balanced-seven closure is reduced to exactly two statements.

## First exact V-branch analytic open

`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`

with target

\[
\int_{\mathbb T^7}\overline{z_1\cdots z_7}
\sum_{q\sim X^{3/5}}\mu(q)
\Delta_{\rm LC}(f_z;X,q,-s\overline2)\,dz
=o(X/\log X).
\]

This is weaker than proving a uniform absolute modulus-average theorem for every `z`: only the degree-`(1,...,1)` signed torus coefficient is required.

## Comparison/source pin

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`

with target

\[
\sum_{q\sim Q}\mu(q)
\bigl(M^{pol}_{7,s}(q)-M_{7,s}(q)\bigr)
=o(X/\log X).
\]

These two statements imply

`AFFINE287-BALANCED7-MODULUS-AVERAGE45 CLOSED`.

## Published-theorem near misses

The source audit records only near-matches, not direct providers:

- the `3/5-epsilon` smooth-multiplicative theorem requires a sufficiently small smoothness exponent without a literal threshold proving `1/7`;
- the stronger smooth-number distribution range has modulus room beyond `3/5`, but its stated smoothness parameter does not literally certify `y=X^(1/7)`;
- P6.3 has the wrong equal-seven range geometry.

## Current ledger

| Node | Status |
|---|---|
| `FORD-GENERATED-DEPTH-N0-287` | PASS, safe `N0=112` |
| exact Vaughan affine-prime source | PASS |
| prime-modulus Möbius two-outer structural map | PASS |
| `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45` | M/Vaughan BRANCH OPEN |
| balanced-seven character parent | PASS |
| separate mult. LS / high moments | NONCLOSING: `X^(1/10)` deficit |
| P6.3 equal-seven dictionary | FALSE |
| prime-box repair | NONEXHAUSTIVE |
| q-Möbius micro-switch | NONEXHAUSTIVE |
| repeated-prime router | PASS: `X^(6/7+o(1))` |
| squarefree torus polarization | PASS |
| smooth multiplicative dictionary | PASS |
| `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` | **FIRST EXACT V-BRANCH ANALYTIC OPEN** |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | SOURCE OPEN |
| balanced-seven | REDUCED, NOT CLOSED |
| model singleton | OPEN after balanced-seven |
| `k=0` smooth parity | OPEN |
| remaining fixed-`g_*` census | OPEN |
| FCL | OPEN |
| Erdős #287 | OPEN |

## Current files

- [`ERDOS287_PENDING_BALANCED7_POLARIZED_EOD_FRONTIER_2026-08-28.md`](ERDOS287_PENDING_BALANCED7_POLARIZED_EOD_FRONTIER_2026-08-28.md)
- [`ERDOS287_NEXT_POLARIZED_OMEGA7_SIGNED_EOD45.md`](ERDOS287_NEXT_POLARIZED_OMEGA7_SIGNED_EOD45.md)
- [`ERDOS287_LATEST_BALANCED7_UPDATE_V15.tex`](ERDOS287_LATEST_BALANCED7_UPDATE_V15.tex)
- [`ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md`](ERDOS287_PENDING_PRIME_MODULUS_MU_TWOOUTER_FRONTIER_2026-08-27.md)
- [`ERDOS287_LATEST_SOURCE_UPDATE_V14.tex`](ERDOS287_LATEST_SOURCE_UPDATE_V14.tex)

## Firewall

The balanced-seven polarization is a source reduction, not an endpoint theorem. The finite Lean result remains unchanged. No claim of balanced-seven closure, `k=0` smooth-parity closure, FCL closure, `WindowPairSupply`, or Erdős #287 is made.
