# ERDŐS #287 PROOF INDEX

Append-only provenance map. Do not delete superseded or retracted entries. The current-state snapshot lives in `CURRENT_FRONTIERS.md`.

Last reconciled: 2026-08-30

---

## Current node

### `287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45`

**Status:** analytic OPEN; current first exact main-line residual.

**Parent:** `SHAREDG0-SIGNED-LEVELPAIR-GRAM45`, strictly reduced by exact shared-gcd Gram reorganisation.

**First deriving research run:** 2026-08-30, “GOLD PIVOT / EXPLOIT 287 — Signed level-pair Gram → product modulus → single Möbius sign → exact one-level operator”.

**Hostile audit:** no final analytic closure claimed. A narrow audit is still required before treating the strict-subpolytope one-level energy estimate as publication-bank closure.

**Formal bank:** product-modulus / shared-gcd Gram-as-square delta should be banked append-only; until that layer is reconciled in the active Aristotle repository, the current node remains research-exact and analytically uninhabited.

**Exact operator:**

\[
\sum_d \frac{\lambda_H(d)}{d^2}
\sum_{a\sim A}\rho(a)
\left|\sum_{m\asymp G/d,(m,d)=1}\frac{\mu(m)}m
\sum_{t\bmod dm}^{*}\widetilde G_{dm,s,\tau}(t)e_{dm}(ta)\right|^2.
\]

**Current bound:**

\[
\frac{(A+G)(GB+B^2)}{H}(\log X)^{o(1)}.
\]

**Required:**

\[
AB^2(\log X)^{-6-2\eta-C_{\rm route}}.
\]

**Sole missing mechanism:** cancellation in the one-level signed Möbius operator `sum_m mu(m)/m V_{dm}(a)` before complete primitive-`t` Ramanujan reassembly neutralises the sign, averaged over the friable `a` source and the exact shared-gcd projector.

**Next attack:** controlled Ramanujan pole/defect separation: isolate the `r=1` local/pole term, determine its existing local owner, and exploit the `r>1`, `r | 2ab+s` signed divisor-defect using progression sparsity and the remaining `mu(r)` sign.

---

## Latest key exact pivot

### `DET1-SHAREDGCD-GRAM-SQUARE45`

**Status:** exact PASS.

Let `Omega_H` select the shared-gcd sector and define

\[
\lambda_H=\mu*\Omega_H.
\]

Möbius inversion gives

\[
\Omega_H((g_1,g_2))
=\sum_{d\mid g_1,\ d\mid g_2}\lambda_H(d).
\]

Hence the two-level signed cross Gram becomes exactly

\[
\mathcal Q_H
=\sum_d\frac{\lambda_H(d)}{d^2}
\sum_a\rho(a)
\left|\sum_m\frac{\mu(m)}mV_{dm}(a)\right|^2
\]

on the squarefree clean sector. This replaces the apparent `G^2/H` pair bookkeeping with harmonic divisor mass plus one signed level variable.

**Research harmonic-mass estimate:** `sum_d |lambda_H(d)|/d^2 << 1/H` under the stated smooth shared-gcd support; formal status depends on the exact Aristotle implementation.

---

## Product-modulus branch

### `DET1-LEVELPAIR-PRODUCTMOD-SIGN45`

**Status:** exact PASS.

For

\[
g_1=g_0r_1,\qquad g_2=g_0r_2,\qquad n=r_1r_2,
\]

with the squarefree/pairwise-coprime source,

\[
\mu(g_1)\mu(g_2)=\mu(r_1)\mu(r_2)=\mu(n),
\qquad
[g_1,g_2]=g_0n.
\]

### `DET1-D-N-COPRIME45`

**Status:** exact PASS.

From primitive frequencies,

\[
D=t_1r_2-t_2r_1
\]

satisfies `(D,n)=1`.

### `DET1-LEVELPAIR-N-DIVISORSPLIT45`

**Status:** exact PASS.

Ordered coprime level pairs are reindexed by a balanced unitary divisor `r | n`, with

\[
\frac1{g_1g_2}=\frac1{g_0^2n}.
\]

### `DET1-FIXEDD-FREQUENCY-RIGIDITY45`

**Status:** exact PASS.

For fixed `D`,

\[
t_1\equiv D\overline{r_2}\pmod{r_1},
\qquad
t_2\equiv-D\overline{r_1}\pmod{r_2},
\]

leaving only the shared `g0` parameter after CRT reconstruction.

The Farey kernel becomes

\[
\Phi_A\!\left(\frac{D}{g_0n}\right),
\]

which is independent of the divisor split `r | n`.

### `DET1-LEVELPAIR-N-RECIPROCAL-NORMALFORM45`

**Status:** exact PASS.

After separating the shared-`g0` component, define `beta_r` by

`beta_r ≡ b1 (mod r)`, `beta_r ≡ b2 (mod n/r)`.

The remaining reciprocal phases combine to

\[
e_n\!\left(sD\overline{2g_0\beta_r}\right).
\]

### `DET1-LEVELPAIR-PRIMEASSIGNMENT45`

**Status:** PASS at fixed squarefree `n` as a two-state prime-assignment product.

**Firewall:** this does **not** give ordinary multiplicativity in `n`, because the local factors contain `inverse(n/p) mod p`. Therefore the single-`mu(n)` coefficient does not supply a direct Euler-product / `1/zeta` route.

### `DET1-LEVELPAIR-SINGLEMOBIUS-N45`

**Status:** analytic OPEN / nonclosing by naive zero-free contour.

Immediate re-expansion of the fixed-`n` prime assignments is representation-equivalent to the original divisor split.

---

## Short-lift and primitive-conductor bank

### `DET1-SHORTLIFT-EULER-COLLAPSE45`

**Status:** NANC-verified research PASS after uniformity repair.

Correct contour:

`Re w = -c0 / sqrt(log Delta)`.

Threshold:

`D_sharp = exp(C_sharp (log log X)^2)`.

The extremal prime-divisor argument gives the finite Euler factor `(log X)^(o(1))` uniformly for polynomial `H`, so polynomially long lifts regain arbitrary fixed logarithmic saving. The previous one-full-log charge is withdrawn.

**Formal firewall:** do not claim the classical zeta zero-free analysis is Lean-proved merely because the exact finite profile algebra is formalised; keep any corresponding analytic input uninhabited unless explicitly formalised.

### Existing/reported formal exact bank

Reported active Aristotle modules from the preceding shared-`g0` repair layer include:

- `RequestProject/CurrentProgramme/LocalProfileHarmonicTwists.lean`
- `RequestProject/CurrentProgramme/SharedG0PrimitiveUParam.lean`
- `RequestProject/CurrentProgramme/SharedG0PrimitiveURouter.lean`
- `RequestProject/CurrentProgramme/SharedG0UnitSectorGcd.lean`
- `RequestProject/CurrentProgramme/SharedG0BPairAveraged.lean`
- `RequestProject/CurrentProgramme/PrimitiveReducedDenominator.lean`
- `RequestProject/CurrentProgramme/PrimitiveNearFreqCount.lean`
- `RequestProject/CurrentProgramme/SharedG0CauchyConfigurationSocket.lean`
- `RequestProject/Status/CurrentStatusErdos287SharedG0Repair.lean`
- `RequestProject/Status/AxiomAuditErdos287SharedG0Repair.lean`
- `ERDOS287_SHAREDG0_CAUCHY_REPAIR_SAFE_BANK_REPORT.md`

If this mirror repository does not yet contain those exact paths, verify the active Aristotle repository/branch before publication and record the resulting commit SHAs here. Do not infer a formal bank merely from this research index.

---

## Cauchy repair history / retractions

### `SHAREDG0-BPAIR-AVERAGED45`

**Status:** local/exact averaged-router PASS.

The primitive shared-`g0` kernel satisfies a pointwise gcd bound, and averaging over the actual `b1,b2` source gives the finite precursor

\[
\sum_{b_1,b_2}(g_0,b_1-b_2)
\lesssim B^2\tau(g_0)+Bg_0.
\]

### `SHAREDG0-CAUCHY-CONFIGURATION45`

**Status:** PASS as a normalisation diagnosis; historical first residual superseded.

Near-set density yields `density^(1/2)` at the Gram level and `density^(1/4)` at the original amplitude level.

### `DET1-LARGESHAREDG0-CELLS45:CLOSED`

**Status:** RETRACTED / OPEN.

**Failure:** the local fixed-pair gain was incorrectly promoted to the full cross-level source; the restored `G^2/H` level-pair multiplicity and first-Cauchy `A` factor remove the claimed global saving.

### `DET1-PRIMITIVE-NEARFREQ45:CLOSED`

**Status:** RETRACTED / NONCLOSING by that Cauchy configuration.

**Failure:** the `density^(1/4)` gain is only relative to an auxiliary unrestricted Gram; after full physical normalisation, the remaining exponent is nonnegative in the relevant regimes.

### `PRIMITIVE-SMALLGCD-FAR-HARDDEN-GRAM45`

**Status:** NOT PROMOTED as the controlling frontier.

---

## One-level energy subpolytope

### `DET1-SHAREDGCD-ONELEVEL-ENERGY45`

**Status:** provisional research closure on a strict subpolytope; hostile promotion audit pending.

Research condition:

\[
\kappa>\max(\alpha,\theta)+\max(\beta,\theta)-1+\delta.
\]

Do not convert this into a publication-bank theorem until the complete normalisation/source ledger passes a narrow audit.

---

## Complete primitive-`t` Ramanujan firewall

### `ONELEVEL-RAMANUJAN-ZEROFREE45`

**Status:** representation loop / NONCLOSING.

For generic `p \nmid N`, `c_p(N)=-1` and `mu(p)c_p(N)=+1`. Thus complete primitive-`t` reassembly neutralises the surviving Möbius sign. Formally the generic Euler structure is pole-like (`zeta(1+w)/zeta(2+2w)`), not a `1/zeta` zero-free source.

**Lesson:** exploit the one-level Möbius sign before full primitive-frequency completion.

---

## Downstream firewall

- `UNIFORM k=0`: OPEN.
- `FCL`: NOT REACHED.
- `N2`, Gate 2, and WindowPairSupply: do not promote until the current analytic descendant is genuinely closed.
- `ERDOS287`: OPEN.

---

## Append template for future runs

For every new node append:

- `NODE:`
- `STATUS:`
- `PARENT:`
- `CHILDREN:`
- `FIRST DERIVED IN:`
- `HOSTILE AUDIT:`
- `FORMAL LEAN MODULE / DECLARATIONS:`
- `COMMIT SHA:`
- `SUPERSEDES / SUPERSEDED BY:`
- `KEY EQUATIONS:`
- `CURRENT BOUND:`
- `REQUIRED BOUND:`
- `SOLE MISSING MECHANISM:`
- `NEXT ATTACK:`

Never erase retractions, nonclosing routes, or superseded frontiers.