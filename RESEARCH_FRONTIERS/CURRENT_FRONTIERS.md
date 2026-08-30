# CURRENT RESEARCH FRONTIERS

Last reconciled: 2026-08-30

Purpose: current-state locator for Gate 1B and Erdős #287. This is not itself a proof. Historical provenance belongs in the append-only proof indexes. The directory is mirrored in both research repositories.

---

## Gate 1B

**Status:** `GATE1B OPEN`

**Current first analytic residual (research-exact; quantitative promotion audit pending):**

`C4SHIFT-BEZOUT-DUAL-R0ELL45`

**Parent strictly reduced:** `C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`.

**Parallel local/source residual:**

`C4SHIFT-BEZOUT-ZEROMODE-LOCALMATCH45`, as the current Bézout-fibre component of `TOPBAND-BROAD-MAJOR-TREE-MATCH45`.

**True target:**

\[
\|\widehat H_j^\perp\|_{L^1_\theta\ell_v^2}\ll Y^{3/4}L^C.
\]

### Latest exact geometry

On the clean determinant-two sector,

\[
(A_i,\ell)=1,\qquad X_i\mid A_i
\]

forces

\[
(d,\ell)=1,
\]

so the previous `g0, d0, ell0` bookkeeping disappears from the analytic child. With

\[
X_1=da,\quad X_2=db,\quad (a,b)=1,
\]

and `r=d r0`, the physical shift is exactly

\[
bZ_2-aZ_1=\ell r_0.
\]

A Bézout parametrisation is

\[
Z_1=\ell r_0\kappa_{a,b}+bt,\qquad
Z_2=\ell r_0\bar b_a+at,
\]

with physical line length `T_d ~ d` in interior packets.

The physical AP condition becomes one residue independent of `r0`:

\[
t\equiv -2\overline{usdab}\pmod\ell.
\]

The run reports a rigidity statement that for fixed `(d,a,b,ell)` at most one physical `(r0,t)` survives. This statement is source-critical and should be checked in the next promotion audit including the possibility that two admissible `t` values differ by a multiple of `ell`.

### Centered t-dual decomposition

The exact cyclic Fourier coefficient of the centered line kernel is

\[
\widehat K_{\rm cent}(\nu)
=
\frac{e_\ell(-\nu\tau)}{\ell}
\left[1-\frac1\ell\sum_{k\bmod\ell}
\mathcal M_1(k+\nu\bar c)\overline{\mathcal M_2(k)}\right],
\]

where `c=dab mod ell` and `tau=A0 inverse(c) mod ell`.

The zero dual mode is **not zero**; it is routed to the local/source branch:

`C4SHIFT-BEZOUT-ZEROMODE-LOCALMATCH45`.

The analytic branch retains only `nu != 0` and has reciprocal phase

\[
e_\ell\!\left(2\nu\overline{usdab}\right)
\]

against the exact shifted two-coordinate gamma source.

After opening

\[
\gamma_j(Z)=\sum_{xy=Z}g_{j,1}(x)g_{j,2}(y),
\]

the source satisfies

\[
bx_2y_2-a x_1y_1=\ell r_0
\]

and the nonzero dual phase can be represented using

\[
e_\ell(\nu t)=e_\ell(\nu\bar b\,x_1y_1).
\]

No literal published/banked Kloosterman provider has yet been matched to this coupled source.

### Provisional quantitative D-census (PROMOTION AUDIT PENDING)

Let

\[
T=Y^{3/2}L^{O(1)},\qquad d\sim D.
\]

The latest run claims the source-energy estimate

\[
\mathcal N_D
\ll
Y^{3/4}\sqrt{\min(D,T/D)}L^C.
\]

Consequences claimed in that run:

- boundary bands `D <= L^B` or `D >= T L^{-B}` close;
- central band `L^B < D < T L^{-B}` remains;
- worst point `D=T^{1/2}=Y^{3/4}` gives achieved `Y^(9/8)` versus required `Y^(3/4)`;
- residual deficit is reduced from `Y^(3/4)=X^(1/12)` to `Y^(3/8)=X^(1/24)`.

These are **provisional analytic promotions** until a narrow hostile audit checks the rigidity/multiplicity step and the row/column norm derivation. Do not yet treat the boundary closure or `X^(1/24)` deficit as publication-banked.

### Current missing mechanism

Joint cancellation of the nonzero `t`-dual reciprocal phase

\[
e_\ell\!\left(2\nu\overline{usdab}\right)
\]

against the exact shifted two-coordinate gamma source, preserving the coupled `r0, ell` family. The kernel itself has no `r0` phase, so any `r0` gain must come from the gamma-line source.

### Do not reopen

- pointwise one-four-product minor norm promotion — retracted;
- scalar minor `L2` energy — natural scale only;
- false additive factorisation of Dirichlet convolution;
- old reciprocal-residue incidence tax;
- `r=0` positive diagonal;
- generic `5/8` BV as a substitute for the source-exact theorem.

### Next action

Before a broader construction run, hostile-audit the D-census promotion: fixed `(d,a,b,ell)` physical multiplicity, alpha/gamma source-energy claims, row/column bounds, boundary-D closure, and the claimed `X^(1/24)` residual. If it passes, attack `C4SHIFT-BEZOUT-DUAL-R0ELL45` directly.

---

## Erdős Problem #287

**Status:** `ERDOS287 OPEN`.

**Uniform `k=0`:** open.  **FCL:** not reached.

**Current first main-line residual:**

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45`.

**Exact operator shape:**

\[
\sum_d\frac{\lambda_H(d)}{d^2}
\sum_{a\sim A}\rho(a)
\left|\sum_{m\asymp G/d}\frac{\mu(m)}mV_{dm}(a)\right|^2.
\]

**Current generic bound:**

\[
\frac{(A+G)(GB+B^2)}H(\log X)^{o(1)}.
\]

**Required:**

\[
AB^2(\log X)^{-6-2\eta-C_{\rm route}}.
\]

Latest structural pivot: the shared-gcd Gram-as-square identity replaces the apparent two-level `G^2/H` pair bookkeeping by harmonic divisor mass plus a one-level signed Möbius `m`-operator. Product-modulus compression also gives `mu(g1)mu(g2)=mu(n)` with `(D,n)=1`, but the fixed-`n` two-state kernel is not ordinarily multiplicative in `n`, so a naive `1/zeta` route is unavailable.

**Retractions:** old `LARGESHAREDG0:CLOSED` and `PRIMITIVE-NEARFREQ:CLOSED` are retracted; the hard-denominator core was not promoted. Complete primitive-`t` Ramanujan reassembly is nonclosing because it neutralises the remaining Möbius sign.

**Provisional audit item:** `DET1-SHAREDGCD-ONELEVEL-ENERGY45` strict-subpolytope closure remains promotion-audit pending.

**Next attack:** split the one-level Ramanujan completion into the `r=1` local-main/pole component and the `r>1`, `r | 2ab+s` divisor-defect, preserving the Möbius resource before complete primitive-`t` reassembly.

---

## Mandatory update rule

Whenever either programme changes frontier, update this file and append the corresponding proof index with status, parent/children, deriving run, hostile-audit status, Lean provenance if banked, supersessions/retractions, key equations, current/required bounds, missing mechanism, and next attack. Never delete historical provenance.