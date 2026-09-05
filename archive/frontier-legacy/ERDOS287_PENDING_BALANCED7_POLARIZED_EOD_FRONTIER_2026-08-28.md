# Erdős #287 — balanced-seven polarized endpoint frontier

**Date:** 28 August 2026  
**Status:** research frontier only; Erdős #287 remains open.

## What changed

The balanced-seven V-branch has now been source-reduced past the raw seven-variable character form.

For

\[
Q=X^{3/5},\qquad Y=X^{1/7},
\]

the exact labelled seven-prime source

\[
\mathcal B_{7,s}(X)
=
\sum_{q\sim Q}\mu(q)
\left[
\sum_{\substack{p_1,\ldots,p_7\sim Y\\2p_1\cdots p_7\equiv-s\;(\bmod q)}}
\prod_{i=1}^{7}\omega_i(p_i)
-\mathfrak M_{7,s}(q)
\right]
\]

has been reduced by exact torus polarization to a family of smooth-supported multiplicative functions.

This does **not** close the M/Vaughan branch. The current programme has two distinct open analytic fronts:

- M/Vaughan branch: `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`;
- balanced-seven V-branch: `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`, together with the comparison pin `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`.

## Death tests now banked at research level

The following routes do not close the balanced-seven cell:

- ordinary separate multiplicative large sieve: `X^(1/10-o(1))` deficit;
- separated higher moments: same `X^(1/10)` deficit;
- equal-seven three-block Pascadi Proposition 6.3 dictionary: false by incompatible exponent inequalities;
- termwise prime-box Vaughan/Heath-Brown repair: nonexhaustive because an unsplit prime term necessarily survives;
- modulus micro-switch as an exhaustive strategy: nonexhaustive because prime `q` has no nontrivial short factor.

## Exact polarization

For `z=(z_1,...,z_7) in T^7`, define on primes `p~Y`

\[
a_z(p)=\frac17\sum_{i=1}^{7}z_i\omega_i(p),
\qquad |a_z(p)|\le1,
\]

and the squarefree-supported multiplicative function

\[
f_z(p)=a_z(p),\qquad f_z(p^\ell)=0\quad(\ell\ge2).
\]

For distinct primes,

\[
[z_1\cdots z_7] f_z(p_1\cdots p_7)
=
7^{-7}
\sum_{\sigma\in S_7}
\prod_{j=1}^{7}\omega_{\sigma(j)}(p_j).
\]

Hence the ordered labelled squarefree source is exactly the torus coefficient

\[
7^7\int_{\mathbb T^7}\overline{z_1\cdots z_7}
\sum_{\substack{n\asymp X\\n\equiv a_s\;(\bmod q)}}f_z(n)W(n/X)\,dz.
\]

Repeated-prime tuples contribute only

\[
O(X^{6/7+o(1)}).
\]

The generalized von Mangoldt coefficients satisfy

\[
|\Lambda_{f_z}(p^\ell)|\le\Lambda(p^\ell),
\]

so this is a genuine smooth-supported multiplicative class uniformly in `z`.

## First exact balanced-seven residual

Let `E_q(f_z;a_s)` denote the principal + low-conductor expected term in the chosen beyond-1/2 convention, and

\[
\Delta_{\rm LC}(f_z;X,q,a_s)
=
\sum_{\substack{n\asymp X\\n\equiv a_s\pmod q}}f_z(n)W(n/X)
-\mathcal E_q(f_z;a_s).
\]

The first exact analytic residual is

`AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45`

with target

\[
\int_{\mathbb T^7}\overline{z_1\cdots z_7}
\sum_{q\sim X^{3/5}}\mu(q)
\Delta_{\rm LC}(f_z;X,q,-s\overline2)\,dz
=
o(X/\log X).
\]

This is weaker than proving a uniform absolute distribution theorem for every `z`: only one signed torus coefficient is required.

## Comparison/source pin

Define the torus-extracted expected term `M^{pol}_{7,s}(q)` from the same principal / low-conductor convention. The comparison branch must prove

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45`

i.e.

\[
\sum_{q\sim Q}\mu(q)
\bigl(M^{pol}_{7,s}(q)-M_{7,s}(q)\bigr)
=o(X/\log X).
\]

These two estimates imply `AFFINE287-BALANCED7-MODULUS-AVERAGE45 CLOSED`.

## Current ledger

| Node | Status |
|---|---|
| balanced-seven character parent | PASS |
| separate multiplicative LS | NONCLOSING: `X^(1/10)` deficit |
| separate high-moment route | NONCLOSING: same deficit |
| P6.3 equal-seven dictionary | FALSE |
| prime-box HB/P6.3 all-cell repair | FALSE / unsplit term survives |
| q-Möbius micro-switch | NONEXHAUSTIVE |
| repeated-prime router | PASS: `X^(6/7+o(1))` |
| squarefree torus polarization | PASS |
| smooth multiplicative class dictionary | PASS |
| `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` | **FIRST EXACT V-BRANCH ANALYTIC OPEN** |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | SOURCE OPEN |
| balanced-seven cell | REDUCED, NOT CLOSED |
| `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45` | M/Vaughan BRANCH OPEN |
| `k=0` smooth parity | OPEN |
| FCL | OPEN |
| Erdős #287 | OPEN |

## Firewall

This is a source reduction, not a proof of the endpoint distribution theorem. No claim of balanced-seven closure, full `k=0` smooth-parity closure, FCL closure, `WindowPairSupply`, or Erdős #287 is made.
