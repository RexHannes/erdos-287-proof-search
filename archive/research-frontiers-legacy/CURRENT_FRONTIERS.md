# CURRENT RESEARCH FRONTIERS

Last reconciled: 2026-08-31

Purpose: current-state locator for Gate 1B and Erdős #287. This is not itself a proof. Historical provenance belongs in the append-only proof indexes. The directory is mirrored in both research repositories where applicable.

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

### C0 — current audited bank

`FIXEDRATIO-BALANCED-b-UNITARYFOURIER45`: **PASS WITH REPAIRS**.

The exact finite contraction is

\[
\eta_b^2\ll L^C\left(\frac{x}{B}+\frac1N+\frac1{E_b}+\frac1x\right).
\]

The product-energy estimate is source-specific to the literal bounded dyadic physical packet; the complete unit branch is

\[
\gcd(b a_\rho b_\rho u_\rho,x)=1,
\]

with complementary nonunit cells routed to D4; and the small-`x` owner is explicit.

Therefore:

```text
EXACT PRODUCT COLLISION: ANALYTICALLY CLOSED
DOUBLE TYPE II: ANALYTICALLY CLOSED
C0: ANALYTICALLY CLOSED / CONDITIONAL ON FORMAL NORMALISATION
```

Formal/source pin:

```text
SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45
```

plus the complete physical Perron/nuclear normalisation unless absorbed into that pin.

### Why the C0 mechanism closes

After canonical reduced-projective conditioning, the Kloosterman kernel is independent of the balanced `b` source. With

\[
b=\ell_b d_b e_b,\qquad d_b,e_b>Y,
\]

combine `n=ell_b d_b`; the reciprocal phase has the form

\[
e_x(C_\Pi\bar n\bar e_b).
\]

Residue aggregation modulo `x` and inversion on unit residues produces a restricted finite Fourier matrix with exact operator norm `sqrt(x)`. Together with residue multiplicities and the fixed-depth source product energy this yields the four-term contraction. No conjectural Möbius cancellation and no new spectral black box are used.

### Transverse — strictly reduced / open

For one packet

\[
R_P=z^2q_Cq_m,
\]

with

\[
q_C=2(e/a_1)(r_2/c_2)b_1^\flat,
\]

and the symmetric primed packet. After row-gcd reduction the reduced conductor is encoded by the corresponding coprime carrier factors.

The naïve full-CRT two-signless DFT is **RETRACTED**: CRT fusion of `q_C` and `q_m` produces cross-modulus inverse coefficients in the numerator.

Banked repair:

```text
THREEFACTOR-TRANSVERSE-ONECONDUCTOR-RECIPROCITY45: PASS
```

For

\[
\Phi_P=e_q(A\overline{rm})e_r(B\overline{qm}),
\]

reciprocating only the `q` component gives

\[
\Phi_P=\operatorname{Arch}_P\,e_{m_P}(\Gamma_P^{\rm red}\bar q),
\]

where

\[
\Gamma_P=-A+mB\overline m\pmod r,
\qquad
g_P=(B-A,r),
\qquad
m_P=rm/g_P,
\]

and `(Gamma_P^red,m_P)=1`.

Banked finite-Fourier theorem:

```text
THREEFACTOR-TRANSVERSE-qC-UNITARYFOURIER45: PASS
```

For a grouping `q=S1*S2`, the relative contraction is

\[
\eta_P^2\ll L^C\left(\frac{m_P}{L_1L_2}+\frac1{L_1}+\frac1{L_2}+\frac1{m_P}\right).
\]

It accepts arbitrary `L^2` coefficient vectors; no Möbius cancellation is required. `Omega_H` is therefore not the analytic blocker at this step; its physical `L^2` normalisation remains a source pin.

The dense-`q_C` compiler is closed on explicit dominance/two-long-group hypotheses. This is a strict subregion, not the whole transverse family.

### Current first analytic residual

```text
THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45
```

**Status:** `OPEN`.

The critical operator retains both packet orientations and the full Bézout-dependent reciprocal numerator. Surviving cells include nondominant `q_C`, nondominant `q_C'`, partitions with one short side, single atomic-carrier dominance, and critical `q ~ r*m` geometry.

The next mathematical run should test whether the missing second Fourier axis can come from the Bézout numerator, an opposite-packet carrier, the `m` variable after `TT*`, a signed-but-`L^2` carrier, grouped short factors, or both source orientations. None is currently proved.

### Parallel b-diagonal

```text
BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : OPEN
```

Keep this separate from the transverse residual.

### Formal / Aristotle checkpoint

The latest completed bank actually supplied for this C0/unitary-Fourier checkpoint records:

```text
default lake build: PASS
8298 jobs
0 errors
```

with axiom reports limited to ordinary Mathlib foundations (`propext`, `Classical.choice`, `Quot.sound`) and no reported `sorry`, custom axiom, `unsafe`, opaque shortcut, `implemented_by`, or `native_decide`.

The named newest modules rely on a dependency graph not yet fully reproduced in public `RequestProject/Main.lean`. Until that dependency-complete graph is imported and rebuilt publicly, the research frontier is deliberately ahead of the public formal-main frontier. No newer one-conductor formal run is invented.

### Retractions / supersessions

- old `n=j inverse(u') mod x` C0 architecture: **RETRACTED**;
- old `1+UU'/B` wrap: **RETRACTED**;
- naïve transverse two-signless DFT: **RETRACTED**;
- `THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45` as first frontier: **SUPERSEDED**;
- R7 `287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45` as the controlling public first frontier: **SUPERSEDED AS CONTROLLING**, with its historical/local research content retained.

---

## Mandatory update rule

Whenever either programme changes frontier, update this file and append the corresponding proof index with status, parent/children, deriving run, hostile-audit status, Lean provenance if banked, supersessions/retractions, key equations, current/required bounds, missing mechanism, and next attack. Never delete historical provenance.