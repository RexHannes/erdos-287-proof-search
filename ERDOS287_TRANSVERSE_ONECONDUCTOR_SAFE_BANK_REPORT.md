# ERDŐS #287 — TRANSVERSE ONE-CONDUCTOR SAFE BANK REPORT

Append-only delta.  No existing declaration was deleted, renamed, weakened, relocated or
overwritten.  `RequestProject/Main.lean` received appended `import` lines only (no reordering,
no deletion).

---

## FILES ADDED

- `RequestProject/CurrentProgramme/Erdos287TransverseReducedConductor.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseOneConductorReciprocity.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseGammaReduction.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseQCUnitaryCompiler.lean`
- `RequestProject/CurrentProgramme/Erdos287TransverseDenseQCInterface.lean`
- `RequestProject/Status/CurrentStatusErdos287TransverseBezoutSingleCarrier.lean`
- `RequestProject/Status/AxiomAuditErdos287TransverseOneConductor.lean`
- `ERDOS287_TRANSVERSE_ONECONDUCTOR_SAFE_BANK_REPORT.md` (this file)

## FILES MODIFIED

- `RequestProject/Main.lean` — seven appended `import` lines, nothing else.

## PREVIOUS BANK REUSED

Reused verbatim, never re-proved:

- `Erdos287.ReciprocalUnitaryFourier.reciprocalUnitaryFourier_bilinear_bound` and its alias
  `transverseTwoCarrierUnitaryFourier`;
- `Erdos287.ReciprocalUnitaryFourier.unitaryFourierKernel` (identified with the new reduced
  arithmetic phase in `reducedPhase_arithmetic_factor`);
- `Erdos287.AffineBilinearReciprocalNumerator.zmod_inv_mul_of_isUnit`;
- `Erdos287.BalancedBUnitaryFourier.ProductConvolutionEnergyHypothesis` and
  `threeCarrierReciprocalFourier_of_productEnergy`;
- `Erdos287.C0PhysicalNormalisation.*` normalisation interfaces (unchanged, still explicit);
- `Erdos287.TransverseCarrier.*` carrier interfaces (unchanged, not marked false);
- the C0 unitary-Fourier and transverse-carrier status ledgers, re-checked by
  `c0_ledger_still_preserved_after_oneConductor` and `previous_transverse_ledger_preserved`.

---

## NEW UNCONDITIONAL THEOREMS (all kernel-checked, no placeholder)

**Transverse source factorisation** (`Erdos287.TransverseReducedConductor`).
`TransversePacket` carries `z, e, a₁, r₂, c₂, b₁Flat, m₂Flat, Δ` with positivity and the two
divisibility fields `a₁ ∣ e`, `c₂ ∣ r₂`.  Derived: `E = e/a₁`, `R = r₂/c₂`, `B₀`, `M₀`,
`δ₂ = gcd(Δ,2)`, `δ_E = gcd(Δ,E)`, `δ_B = gcd(Δ,B₀)`, `2° = 2/δ₂`, `E° = E/δ_E`, `B° = B₀/δ_B`,
`q̄ = 2° E° R B°`, `q_m = M₀`, `R̂_P = z² q̄ M₀`.
Exactness theorems: `E_mul_a1`, `R_mul_c2`, `twoCirc_mul_delta2`, `ECirc_mul_deltaE`,
`BCirc_mul_deltaB`, `qBar_mul_deltas` (`q̄ · δ₂ δ_E δ_B = q_C`), `qBar_dvd_qC`, plus positivity
(`E_pos`, `R_pos`, `twoCirc_pos`, `ECirc_pos`, `BCirc_pos`, `qBar_pos`, `RHat_pos`) and
`RHat_eq`.  No division is taken without a divisibility proof.

**Primed packet.**  `primed_packet_symmetric` — the primed packet is an inhabitant of the *same*
structure, so `z'`, `q̄'`, `M₀'`, `R̂_{P'}` need no duplicated definitions.

**Cross-packet reduced conductor.**  `lcm_eq_mul_div_gcd` (`lcm(a,b) = ab/gcd(a,b)`, from
Mathlib's `Nat.gcd_mul_lcm`), `QStar`, `dStar`, `QStarRed`, `QStar_pos`, `dStar_dvd_QStar`,
`QStarRed_mul_dStar`, and the two normal forms
`QStarRed_exact_normal_form` (`Q_*^red · (gcd(R̂_P,R̂_{P'}) · d_*) = R̂_P R̂_{P'}`) and
`QStarRed_eq_div` (`Q_*^red = R̂_P R̂_{P'} / (gcd · d_*)`, for `B_* > 0`).

**Carrier metadata.**  `PacketFactor`, `CarrierClass`, `carrierClass`, `carrierClass_table`
(`E°, R` signless; `B°, M₀` signed/Möbius-bearing; `z², 2°` fixed/structural),
`carrierClass_is_metadata`.  No length or analytic property is encoded.

**`R`-carrier harmonic energy.**  `Rcarrier_harmonic_square_bound`:
`∑_{R ∈ [L,2L)} |1/(c₂R)|² ≤ 1/(c₂² L)` (explicit constant `C = 1`), elementary and finite.

**One-conductor reciprocity** (`Erdos287.TransverseOneConductor`).
`intGcd_congr`, `exists_inverse_of_coprime` (existence of `t` with `m t ≡ 1 (mod r)` from
`gcd(m,r) = 1` — never assumed silently), `transverseGammaInt` (`Γ = -A + m B t`),
`transverseGammaInt_modEq_m`, `transverseGammaInt_modEq_r`, and the requested `ZMod (r m)`
formulations `transverseGamma_mod_m` (`Γ ↦ -A` in `ZMod m`) and `transverseGamma_mod_r`
(`Γ ↦ B - A` in `ZMod r`).  Phase interface: `reducedPhase`, `reducedPhase_norm`
(`‖Φ_P‖ = ‖Arch_P‖`), `reducedPhase_arithmetic_factor`.

**Γ gcd normal form and reduction** (`Erdos287.TransverseGammaReduction`).
`gP = gcd(B-A,r)`, `gP_pos`, `gP_dvd_r`, `gP_dvd_rm`,
`transverseGamma_gcd_eq` (`gcd(Γ, r m) = gcd(B-A, r)`), `gP_dvd_gamma`,
`mP = r m / g_P`, `transverseGammaRed = Γ / g_P`, `mP_mul_gP`, `mP_pos`,
`transverseGammaRed_mul_gP`, and the two principal new theorems
`transverseGammaRed_coprime` (`gcd(Γ^red, m_P) = 1`) and
`transverseGammaRed_isUnit` (`Γ^red` is a unit of `ZMod m_P`).
Bundled: `OneConductorData` with `gcd_normal_form`, `gammaRed_coprime`, `gammaRed_isUnit`,
`modP_pos`, `modP_neZero`.

**`q_C` unitary compiler** (`Erdos287.TransverseQCUnitary`).
`inv_mul_factorisation_zmod` (`q = S₁S₂` units ⟹ `q⁻¹ = S₁⁻¹S₂⁻¹`, reusing the bank),
`natCast_isUnit_of_coprime`, `inv_mul_factorisation_zmod_nat` (explicit coprimality hypotheses),
`transverseQCUnitaryFourier_bound` and `transverseQCUnitaryFourier_l2_bound` (the banked Fourier
theorem instantiated at `(m_P, Γ^red)`; the unit hypothesis on the numerator is *proved*, so
these are unconditional given the packet), `transverseQCUnitary_omegaH_blind`,
`QBarPartition`, `qBarPartition_trivial`, `qBarPartition_nontrivial_not_automatic`.

**Finite sanity tests.**  `transverseGamma_test_r5_m3` (Γ congruences),
`gammaReduction_test_r10_m3` (`Γ = 104`, `g_P = 2`, `gcd(104,30) = 2`, `Γ^red = 52`, `m_P = 15`,
`gcd(52,15) = 1`), `inv_mul_factorisation_test` (`12⁻¹ = 3⁻¹·4⁻¹` in `ZMod 35`, composite
modulus).

## NEW CONDITIONAL COMPILERS (every analytic input an explicit hypothesis)

- `transverseQCGroupedUnitary_of_productEnergy` — grouped/product-aggregated `q_C` compiler.
  Inputs: unit supports, fibre multiplicities `M_N, M_E`, the **explicit** reused
  `ProductConvolutionEnergyHypothesis`, and an explicit `ℓ²` budget.  No source partition is
  claimed to satisfy them automatically.
- `denseQC_closed_of_unitary_margin` — purely logical dense-`q_C` compiler; the antecedent
  contains the `ℓ²` budgets and the margin inequality `m_P E₁ E₂ ≤ target` explicitly.  Its
  conclusion is a finite inequality, never "transverse closed" and never Erdős #287.
- `DenseQCAdmissible` — the dense criterion as explicit finite inequalities (`margin` stands for
  `L^{K_T}`; group lengths are supplied reals with explicit lower bounds).  Proved non-vacuous
  (`denseQCAdmissible_not_automatic`) and separated from the Fourier margin
  (`denseQC_admissibility_does_not_give_the_bound`, `denseQC_margin_not_automatic`).

---

## C0 REPAIR STATUS

Recorded, not re-proved:

- **A. Source-specific product energy.**  The physical balanced-`b` convolution statement is for
  the literal bounded dyadic source packet; it is *not* promoted to an arbitrary-vector
  Dirichlet-convolution theorem.  In Lean it exists only as the explicit hypothesis shell
  `ProductConvolutionEnergyHypothesis`, proved non-automatic.
- **B. Full unit firewall.**  The unitary branch requires `gcd(b · a_ρ · b_ρ · u_ρ, x) = 1`; the
  complementary owner (`gcd > 1`) is D4.  Formally only the arithmetic firewall
  `Erdos287.BalancedBUnitaryFourier.coprime_product_all` exists; the routing itself is not proved.
- **C. `x` versus `X`.**  The exact finite contraction contains `1/x`, hence `x^{-1/2}`, not
  literally `X^{-1/2}`; the source has a separate short-`x`/short-conductor router.  `x` and `X`
  are never identified in Lean (`inv_sqrt_comparison_not_automatic`).
- **D.** C0 status remains **ANALYTICALLY CLOSED, CONDITIONAL ON FORMAL NORMALISATION**
  (`c0Status = conditionalSourcePin`, `c0_still_conditional`).

## TRANSVERSE SOURCE FACTORISATION

`R_P = z² q_C q_m`, `q_C = 2 (e/a₁)(r₂/c₂) b₁Flat`, `q_m = m₂Flat`; after row-gcd reduction
`q̄ = 2° E° R B°` and `R̂_P = z² q̄ M₀`, all with proved exact divisions.  **PASS.**

## ONE-CONDUCTOR RECIPROCITY

Only the `q`-component is reciprocated.  `Γ = -A + m B t` modulo `r m`, with
`Γ ≡ -A (mod m)` and `Γ ≡ B - A (mod r)` proved in both the `Int.ModEq` and the `ZMod`
formulations.  The Archimedean transform is *not* formalised: `reducedPhase` carries it as an
explicit complex parameter, and `reducedPhase_norm` isolates the arithmetic factor.  **PASS.**

## GAMMA REDUCTION

`gcd(Γ, r m) = gcd(B-A, r) = g_P` is derived from `Γ ≡ -A (mod m)`, `gcd(A,m) = 1` and
`Γ ≡ B - A (mod r)`.  Honest scope note: the frequently quoted extra hypothesis `gcd(r,m) = 1`
is **not needed** for the gcd normal form and is therefore not assumed; `gcd(m,r) = 1` is used
only where it is genuinely needed, namely for the *existence* of the inverse `t`
(`exists_inverse_of_coprime`).  No coprimality is assumed silently anywhere.
`m_P = r m / g_P`, `Γ^red = Γ / g_P` (both divisions proved exact) and
`gcd(Γ^red, m_P) = 1`.  **PASS.**

## qC UNITARY COMPILER

`transverseQCUnitaryFourier_bound` is the banked
`reciprocalUnitaryFourier_bilinear_bound` instantiated at modulus `m_P` and numerator `Γ^red`.
No new Fourier proof exists in this delta.  **PASS.**

## OMEGA_H-BLINDNESS

`transverseQCUnitary_omegaH_blind`: since the finite theorem quantifies over arbitrary
coefficient vectors, the bound depends on the coefficient family only through its `ℓ²` mass.  A
supplied `Ω_H` with an explicit `ℓ²` bound is accepted; no physical `Ω_H` `ℓ²` bound is invented
or proved here — the existing normalisation interface remains the owner.  **PASS.**

## DENSE-qC STATUS

`THREEFACTOR-TRANSVERSE-DENSE-qC-COMPILER45: CLOSED ON ITS EXPLICIT HYPOTHESES.`  This is a
research-bank conclusion, not an unconditional Lean theorem about the physical source.

## SUPERSEDED FRONTIER

`THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45` is preserved (its historical row
in `CurrentStatusErdos287TransverseCarrier` is untouched and still reads `open_`) and marked
`superseded` **as first frontier** in the new ledger
(`carrierFactorizationPairExistenceStatus = superseded`).  Its underlying carrier interfaces are
*not* marked false.

## CURRENT FRONTIER

`THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45 : OPEN`
(`transverseCriticalBezoutSingleCarrierStatus = open_`).
The naive signless-pair DFT of the fused `q_C · q_m` modulus is recorded as
`RETRACTED / INVALID AS A SOURCE DICTIONARY` (`naive_full_crt_dft_retracted`); no universal
non-equality theorem is asserted.  The critical (survivor) polytope is `criticalPolytopeStatus =
open_`, with the survivor conditions recorded only as a label datatype.

## B-DIAGONAL FIREWALL

`BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : OPEN / UNTOUCHED` (`bdiagonal_firewall`).  No `q_C`
Fourier theorem is applied to it and no C0 or transverse saving is credited to it
(`no_double_spending_after_oneConductor`).

## AXIOM AUDIT

`RequestProject/Status/AxiomAuditErdos287TransverseOneConductor.lean` runs `#print axioms` for
every declaration of this delta (134 `#print axioms` queries).  Result: every declaration depends
only on a subset of `propext`, `Classical.choice`, `Quot.sound`; 58 depend on no axioms at all.  No
`sorryAx`, no custom axiom, no `unsafe`, no `opaque` shortcut, no `implemented_by`, no
`native_decide`.  A token scan of all new files finds none of `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, `native_decide`, `implemented_by` as code (only inside docstring prose).

## BUILD STATUS

Each new module builds individually: PASS.
Default `lake build`: **PASS — 8305 jobs, 0 errors.**  No unrelated legacy module was modified.

## CURRENT ERDOS287 LEDGER

PERMANENT FORMAL BANK: canonical reduced-projective arithmetic; reciprocal finite Fourier Gram;
reciprocal unitary Fourier bilinear theorem; residue aggregation; balanced reciprocal Fourier
compiler; affine/bilinear reciprocal numerator algebra; C0 normalization interfaces; transverse
carrier interfaces; **new** reduced-conductor arithmetic; **new** one-conductor Γ
congruence/reduction theorems; **new** `q_C` unitary compiler.

- C0: ANALYTICALLY CLOSED, CONDITIONAL ON FORMAL NORMALISATION.
- EXACT PRODUCT COLLISION: ANALYTICALLY CLOSED.
- DOUBLE TYPE II: ANALYTICALLY CLOSED.
- TRANSVERSE BANK: ONECONDUCTOR-RECIPROCITY45 PASS; qC-UNITARYFOURIER45 PASS;
  DENSE-qC-COMPILER45 CLOSED ON EXPLICIT HYPOTHESES.
- TRANSVERSE: STRICTLY REDUCED / OPEN.
- CURRENT FIRST ANALYTIC RESIDUAL:
  THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45.
- PARALLEL: BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45: OPEN.
- FIRST FORMAL SOURCE RESIDUAL: SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45, plus the complete
  Perron/nuclear normalization.
- ERDOS287: **OPEN.**

---

## STRICT FINAL OUTPUT

```
FILES ADDED:                      7 Lean modules + this report (listed above)
FILES MODIFIED:                   RequestProject/Main.lean (7 appended imports only)
PREVIOUS C0 UNITARY BANK:         PRESERVED
C0 FULL UNIT FIREWALL:            RECORDED (gcd(b a_rho b_rho u_rho, x) = 1; complement = D4)
C0 x-vs-X FIREWALL:               RECORDED (1/x, x^(-1/2); x and X never identified)
TRANSVERSE qC FACTORISATION:      PASS
REDUCED PACKET CONDUCTOR:         PASS
CROSS-PACKET QSTARRED:            PASS
ONE-CONDUCTOR RECIPROCITY:        PASS
GAMMA MOD m:                      PASS
GAMMA MOD r:                      PASS
GAMMA GCD REDUCTION:              PASS
GAMMARED COPRIME:                 PASS
q=S1*S2 INVERSE FACTORISATION:    PASS
qC UNITARY COMPILER:              PASS
OMEGA_H-BLIND FINITE THEOREM:     PASS
DENSE-qC CONDITIONAL COMPILER:    PASS
NAIVE FULL-CRT SIGNLESS DFT:      RETRACTED
SUPERSEDED FRONTIER:              THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45
CURRENT FIRST ANALYTIC FRONTIER:  THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45
B-DIAGONAL:                       OPEN / UNTOUCHED
C0 STATUS:                        ANALYTICALLY CLOSED CONDITIONAL ON FORMAL NORMALISATION
TRANSVERSE STATUS:                STRICTLY REDUCED / OPEN
ERDOS287:                         OPEN
AXIOM AUDIT:                      propext / Classical.choice / Quot.sound only; no sorryAx
NEW MODULE BUILD:                 PASS (each module individually)
DEFAULT lake build:               PASS (8305 jobs, 0 errors)
DOUBLE-SPENDING AUDIT:            PASS
STRONGEST SAFE NEW FORMAL BANK:   exact q_C/R̂_P/Q_*^red arithmetic; Γ mod m and mod r;
                                  gcd(Γ, r m) = gcd(B-A, r); gcd(Γ^red, m_P) = 1 and the
                                  unit-ness of Γ^red; the q_C unitary Fourier instantiation at
                                  (m_P, Γ^red) with Ω_H-blind ℓ² dependence
FINAL FORMAL VERDICT:             SAFE APPEND-ONLY BANK UPDATED
```

### Hostile-audit checklist

1. No existing theorem changed — only additions and appended imports.
2. C0 is not encoded as unconditional closure (`c0Status = conditionalSourcePin`).
3. `Ω_H` normalisation remains an explicit interface; no pointwise formula is used.
4. Perron/nuclear normalisation remains explicit.
5. The naive full-CRT signless DFT is not revived; only the retraction is recorded.
6. One-conductor reciprocity uses the modulus `r m` (and, after reduction, `m_P = r m / g_P`).
7. `Γ ≡ -A (mod m)` and `Γ ≡ B - A (mod r)` are proved, in both formulations.
8. The reduction uses the exact gcd `g_P = gcd(B-A,r) = gcd(Γ, r m)`.
9. No unproved coprimality is assumed: `gcd(A,m) = 1` is an explicit hypothesis, `gcd(m,r) = 1`
   is used only for the existence of `t`, and `gcd(r,m) = 1` is not assumed at all.
10. The `q = S₁S₂` inverse factorisation carries explicit unit (or coprimality) assumptions.
11. The Fourier theorem is reused, not duplicated.
12. Dense-`q_C` closure remains conditional on explicit length/margin hypotheses.
13. No theorem states that every transverse packet has two long carriers.
14. No theorem states that the single-carrier residual is empty.
15. Carrier-factorisation metadata asserts no analytic length.
16. The `b`-diagonal row stays separate and open.
17. Erdős #287 remains open.
