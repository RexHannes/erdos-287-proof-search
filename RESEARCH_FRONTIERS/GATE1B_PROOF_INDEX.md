# GATE 1B PROOF INDEX

Append-only provenance map. Do not delete superseded or retracted entries. The current-state snapshot lives in `CURRENT_FRONTIERS.md`.

Last reconciled: 2026-08-30

---

## Current node

### `C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`

**Alias:** `C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45`

**Status:** analytic OPEN; first exact Gate 1B analytic residual.

**Parent:** `C4SHIFT-ONE-MINOR-PUSHED-ENERGY45`.

**Parallel child required for upstream closure:** `TOPBAND-BROAD-MAJOR-TREE-MATCH45` (local/source OPEN).

**First deriving research run:** 2026-08-30, “GOLD CLOSE / EXPLOIT 1B — One-minor pushed AP-index energy”.

**Hostile audit:** no analytic closure claimed; no new NANC required merely for this narrowing.

**Formal bank:** centered-AP/Bézout delta should be banked append-only; until that delta is reconciled in this repository, treat the current node as research-exact but analytically uninhabited.

**Key equations:**

\[
\mathscr R_{1m}=\mathscr R_{\rm full}-\mathscr R_{\rm MM},
\]

\[
\mathscr R_{\rm full}(A_1,A_2)
=1_{A_1\equiv A_0\,(\ell)}1_{A_2\equiv A_0\,(\ell)},
\]

\[
X_2Z_2-X_1Z_1=\ell r,\qquad r\ne0,
\]

and after the gcd split

\[
bZ_2-aZ_1=\ell_0r_0,
\qquad
Z_1=Z_1^{(0)}+bt,
\qquad
Z_2=Z_2^{(0)}+at.
\]

**Current bound:** `Y^(3/2) L^(C0)`.

**Required:** `Y^(3/4) L^C`.

**Deficit:** `Y^(3/4)=X^(1/12)`.

**Sole missing mechanism:** square-root dispersion for the actual centered, nonzero-shift `2+2` multiplicative convolution on the physical `5/8` AP family, after subtraction/routing of the small-modulus local-major profile.

**Next attack:** Bézout-line Fourier/Poisson dispersion; identify the zero dual mode and route it to the local model if exact; then exploit nonzero dual frequencies using the `d`-fibre and `r0/ell0` family.

---

## Immediate parent layer

### `C4SHIFT-ONE-MINOR-PUSHED-ENERGY45`

**Status:** STRICTLY REDUCED; no longer the first exact residual.

**Research target:**

\[
\int_{\mathbb T}\Bigl(\sum_v|\widehat H_j^{1m}(\theta,v)|^2\Bigr)^{1/2}\,d\theta
\ll Y^{3/4}L^C.
\]

**Exact reduction achieved:** one-minor Fourier operator is an exact centered AP kernel, with canonical `mM`, `Mm`, `mm` owners and physical `2+2` shifted geometry.

**Reported formal bank from the leafwise Aristotle layer:**

- `Gate1B/C4ShiftLeafwiseOneMinor.lean`
- `Gate1B/CurrentStatusGate1BC4ShiftLeafwise.lean`
- `Gate1B/AxiomAuditGate1BC4ShiftLeafwise.lean`
- `GATE1B_C4SHIFT_LEAFWISE_ONE_MINOR_SAFE_BANK_REPORT.md`

The reported formal layer proves deterministic major ownership, character diagonalisation, unit/nonunit reduction, legal multiplicative factorisation, leaf classification, tuple-level one-minor split, `(h,K)` normal form, and the `ell`-normalisation firewall, while leaving analytic sockets uninhabited. Verify exact module paths/commit SHAs against the active Aristotle working repository before publication if that working repository differs from this mirror.

---

## Exact structural nodes to preserve

### `C4SHIFT-1M-APKERNEL45`

**Status:** exact PASS.

**Content:** with `h=k1-k2`, `K=k1+k2`, the AP phase is

\[
\Phi=k_1(A_1-A_0)-k_2(A_2-A_0).
\]

Full complete sums force both copies into the physical determinant-two AP residue.

### `C4SHIFT-1M-CENTERED-KERNEL45`

**Status:** exact PASS.

**Content:** sampled double-major operator tensorises, and one-minor is exactly `full - double-major`.

### `C4SHIFT-MAJORPROJECTOR-HKFOURIER45`

**Status:** exact Fourier/aliasing PASS at the algebraic level.

**Content:** sampled major operator aliases ordinary Fourier coefficients over residue classes modulo `ell`; the gain is Fourier structure, not a fake `1/ell^2` state-count saving.

### `C4SHIFT-DOUBLEMAJOR-TO-LOCALMATCH45`

**Status:** source-decomposition PASS; not analytic Gate closure.

**Meaning:** for `j<5`, nonprincipal defect pieces are analytic-small at research level while principal pieces are local profiles; for `j=5`, the all-major leaf is an explicit local model. Physical equality with the historical/canonical top-band local model remains a separate source comparison.

### `TOPBAND-BROAD-MAJOR-TREE-MATCH45`

**Status:** parallel local/source OPEN.

**Role:** must close independently before `C4SHIFT-QFOURIER-PUSHFORWARD45` can be promoted upstream even if the analytic centered AP child closes.

---

## Retractions / firewalls

### `C4SHIFT-ONE-FOURPRODUCT-MINOR45:CLOSED`

**Status:** RETRACTED.

**Reason:** the pointwise minor bound

`|F4(omega)| <= Y^4 L^(-B+O(1))`

does not propagate through the required `L1_theta l2_v` norm. It is a fixed `Y^2=X^(2/9)` worse than the natural RMS/L1 scale in the attempted substitution.

**Do not mark the underlying pointwise bilinear estimate false.** The invalid step is the norm promotion.

### False additive four-product factorisation

**Status:** FALSE / SUPERSEDED.

Dirichlet convolution does not factor under additive Fourier transform. The legal source is

\[
\mathcal F_{4,j}(\omega)
=\sum_{X,Z\asymp Y^2}\alpha_j(X)\gamma_j(Z)e(-\omega XZ),
\]

and multiplicative-character diagonalisation is available only after small-denominator major localisation.

### `ell^{-2}` cardinality firewall

For each `ell`, the two AP indices consume the `1/ell^2` normalisation. No automatic analytic saving exists from that factor alone.

### `r=0` firewall

The positive product diagonal was routed upstream. Current `GammaSharp`/one-minor source must impose `r != 0` at the underlying tuple level, never via a post-summed `r` indicator.

---

## Upstream map

If and only if the current analytic centered-AP child **and** the parallel local match both close, the intended compiler is:

`C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`
→ `C4SHIFT-ONE-MINOR-PUSHED-ENERGY45 CLOSED`
→ `C4SHIFT-QFOURIER-PUSHFORWARD45 CLOSED`
→ `BETAU2-RECIPROCAL-RESIDUE-RESTRICTION45 CLOSED`
→ determinant/Ramanujan/top-band analytic descendants.

Do not skip the local-match branch, and do not run `PURE5` until all literal top-band descendants are closed.

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

Never erase retractions or superseded proof paths.