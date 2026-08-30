# CURRENT RESEARCH FRONTIERS

Last reconciled: 2026-08-30

Purpose: this file is the current-state locator for the active Gate 1B and Erdős #287 programmes. It is not itself a proof. It should be updated whenever a frontier name, status, bound, or immediate child changes. Historical provenance belongs in the two append-only proof indexes in this directory.

Mirror rule: the same research-frontier directory is mirrored in both `twin-prime-proof-search` and `erdos-287-proof-search`. If they ever disagree, reconcile before the next proof run and keep the newest reconciled timestamp only after checking both programmes.

---

## Gate 1B

**Status:** `GATE1B OPEN`

**Current first analytic residual:**

`C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`

**Source-exact alias:**

`C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45`

**Parallel local/source residual:**

`TOPBAND-BROAD-MAJOR-TREE-MATCH45` — source open / not yet closed.

**True analytic target:**

\[
\int_{\mathbb T}\Bigl(\sum_v |\widehat H_j^{\,\perp}(\theta,v)|^2\Bigr)^{1/2}\,d\theta
\ll Y^{3/4}L^C.
\]

**Current generic/source-energy scale:** `Y^(3/2) L^(C0)`.

**Signed deficit:** `Y^(3/4) = X^(1/12)`.

### Latest exact reduction

The one-minor Fourier problem has been physicalised into a centered AP discrepancy:

\[
\mathscr R_{1m}=\mathscr R_{\rm full}-\mathscr R_{\rm MM},
\]

with

\[
\mathscr R_{\rm full}(A_1,A_2)
=1_{A_1\equiv A_0\,(\ell)}1_{A_2\equiv A_0\,(\ell)}.
\]

The physical `2+2` source satisfies

\[
X_2Z_2-X_1Z_1=\ell r,\qquad r\ne0,
\]

and after

\[
X_1=da,\quad X_2=db,\quad (a,b)=1,
\]

plus the gcd split of `d` and `ell`, the collision fibre becomes the literal Bézout line

\[
bZ_2-aZ_1=\ell_0r_0,
\]

with

\[
Z_1=Z_1^{(0)}+bt,\qquad Z_2=Z_2^{(0)}+at.
\]

Thus the first analytic problem is square-root dispersion for the actual centered, nonzero-shift `2+2` multiplicative-convolution source at the exact `5/8` AP level, not a scalar minor-arc estimate.

### Do not reopen / do not reuse as closure

- `C4SHIFT-ONE-FOURPRODUCT-MINOR45:CLOSED` — **RETRACTED**.
- Pointwise four-product minor supremum — valid only as a pointwise estimate; power-nonclosing for the pushed norm.
- Scalar minor `L2` energy — natural scale only.
- False additive factorisation of a Dirichlet convolution — **FALSE / SUPERSEDED**.
- Old reciprocal-residue incidence tax — removed by the `q,v` pushforward; do not charge it again.
- `r=0` positive diagonal — already routed upstream; current source keeps `r != 0` at tuple level.

### Next analytic attack

Bézout-line Fourier/Poisson dispersion; determine whether the zero dual mode is exactly the local-major model, then exploit only the nonzero dual frequencies using the `d`-fibre, `r0/ell0` averaging, actual `alpha_j/gamma_j` source, and the top-band condition.

---

## Erdős Problem #287

**Status:** `ERDOS287 OPEN`

**Uniform `k=0`:** open.

**FCL:** not reached.

**Current first main-line residual:**

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45`

**Exact current operator shape:**

\[
\sum_d \frac{\lambda_H(d)}{d^2}
\sum_{a\sim A}\rho(a)
\left|\sum_{m\asymp G/d}\frac{\mu(m)}m V_{dm}(a)\right|^2.
\]

Here the primitive `t` family, reciprocal `b` source, friable `a` weight, harmonic/Perron parameters, and shared-gcd projector must be retained.

**Current generic bound:**

\[
\frac{(A+G)(GB+B^2)}{H}(\log X)^{o(1)}.
\]

**Required bound:**

\[
AB^2(\log X)^{-6-2\eta-C_{\rm route}}.
\]

### Latest exact reduction

The old signed two-level pair problem has been reorganised exactly by a shared-gcd projector. With

\[
\lambda_H=\mu*\Omega_H,
\qquad
\Omega_H((g_1,g_2))
=\sum_{d\mid g_1,\ d\mid g_2}\lambda_H(d),
\]

one gets the one-level signed operator above. The apparent `G^2/H` pair combinatorics is replaced by harmonic divisor mass (research-level `~ 1/H`) plus a single Möbius `m`-family.

A complementary product-modulus compression also gives, for

\[
g_1=g_0r_1,\quad g_2=g_0r_2,\quad n=r_1r_2,
\]

\[
\mu(g_1)\mu(g_2)=\mu(n),\qquad (D,n)=1,
\]

and the Farey kernel is

\[
\Phi_A\!\left(\frac{D}{g_0n}\right),
\]

independent of the divisor split `r | n`. Fixed-`n` prime assignment is a two-state product, but the resulting coefficient is not ordinarily multiplicative in `n` because local phases contain `inverse(n/p) mod p`; therefore a naive `1/zeta` single-`mu(n)` contour is unavailable.

### Verified / surviving structural results

- Short-lift Euler uniformity repair — NANC-verified research pass with `eta = c/sqrt(log D)` and `D_sharp = exp(C (log log X)^2)`; corresponding Lean analytic input remains uninhabited unless separately formalised.
- Primitive Ramanujan / local-profile finite algebra — banked in the formal programme.
- Shared-`g0` primitive `u` router and averaged `b1,b2` gcd identities — exact finite core survives.
- Reduced denominator algebra `(D,Lambda) | g0` and `den(D/Lambda) >= g1 g2 / g0^2` — exact.
- Shared-gcd Gram-as-square — latest key exact structural pivot.

### Retracted / nonclosing routes

- `DET1-LARGESHAREDG0-CELLS45:CLOSED` — **RETRACTED / OPEN** after restoring full cross-level normalisation.
- `DET1-PRIMITIVE-NEARFREQ45:CLOSED` — **RETRACTED / NONCLOSING BY THAT CAUCHY ROUTE**; final amplitude density exponent is `1/4`, but outer normalisation removes the claimed physical saving.
- `PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45` — **NOT PROMOTED** as the current residual.
- Single-`mu(n)` ordinary Euler-product route — nonclosing.
- Complete primitive-`t` Ramanujan zero-free route — nonclosing / representation loop: generic local Ramanujan sign neutralises the remaining Möbius sign and produces a zeta-pole structure rather than a `1/zeta` zero.

### Provisional research result requiring hostile promotion audit

`DET1-SHAREDGCD-ONELEVEL-ENERGY45` closes a strict exponent subpolytope at research level when

\[
\kappa>\max(\alpha,\theta)+\max(\beta,\theta)-1+\delta,
\]

but this should remain labelled provisional until a narrow promotion audit verifies the complete source-normalisation ledger.

### Next analytic attack

Exploit the one-level Möbius sign **before** complete primitive-`t` Ramanujan reassembly neutralises it. First split the exact Ramanujan completion into the `r=1` pole/local-main term plus the `r>1`, `r | 2ab+s` divisor-defect; determine whether the `r=1` term has an existing local owner, then exploit the progression sparsity and signed divisor structure of the defect.

---

## Mandatory update rule

Whenever either programme changes frontier, update this file and append an entry to the corresponding proof index with:

- exact status;
- parent and immediate children;
- first deriving report/run;
- hostile-audit status;
- formal Lean module/declarations if banked;
- commit SHA when verified in the repository;
- superseded/retracted predecessors;
- key equations;
- current bound;
- required bound;
- sole missing mechanism;
- next attack.

Never delete historical provenance from the proof indexes.