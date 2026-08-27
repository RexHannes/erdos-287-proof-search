# Erdős #287 — prime-modulus Möbius two-outer frontier

**Date:** 27 August 2026  
**Status:** first source-clean analytic frontier; open.

The latest source audit supersedes the generic determinant-one hybrid as the controlling statement. Starting from the actual affine prime source `Lambda(2mn+s)`, `s=±1`, the exact Vaughan Type-II term leaves a prime outer variable and a truncated-Möbius cofactor.

## Source-exact packet

For a dyadic cell,

\[
\mathcal R_{\pi,s}^{(2)}(P;D,R)
=
\sum_{p\sim P}(\log p)
\sum_{\substack{m\sim M,\ n\sim N\\2mn\equiv-s\pmod p}}
\xi_\pi(m)\kappa_\pi(n)
\Delta^{\mu,1}_{D,R}\!\left(\frac{2mn+s}{p}\right)
-\mathfrak M_{\pi,s},
\]

with

\[
\Delta^{\mu,1}_{D,R}(u)
=
\sum_{\substack{dr=u\\d\sim D,\ r\sim R}}
\mu(d)W_D(d)W_R(r).
\]

The ranges are

\[
X^{\sigma/3}<M\le X^\sigma<X^{1/6},\qquad MN\asymp X,
\]
\[
P,D>X^{1/3-o(1)},\qquad PDR\asymp X,\qquad R<X^{1/3+o(1)}.
\]

The generated long coefficient `kappa_pi` has fixed depth; in the `k=0` branch the safe bound is at most 39 generated factors.

## Required theorem

Programme label:

`AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`.

Required saving:

\[
|\mathcal R_{\pi,s}^{(2)}|=o(X/\log X),
\]

or a sufficiently small fixed constant multiple compatible with the fixed Ford-certificate margin.

## Firewalls

- `AFFINE287-DET1-HYBRID-MQ45` is retained only as superseded geometry.
- `lambda_U` is not a general well-factorable dyadic modulus weight.
- the direct canonical Gate-1A determinant dictionary fails;
- no direct native-QK56 dictionary has been established;
- common-conductor covariance is at most a possible high-conductor child after new source-adapter/stability work;
- `VAUGHAN-TYPEI-GENERATED-KAPPA45` remains a separate open adapter;
- closing this theorem would close only the current `k=0` prime-outer parity child, not the entire fixed-certificate leakage family or Erdős #287.
