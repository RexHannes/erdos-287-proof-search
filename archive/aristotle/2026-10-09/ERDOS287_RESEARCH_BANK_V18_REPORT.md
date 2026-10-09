# Erdős #287 — Research Bank V18 report: reciprocal colour algebra

**Erdős #287 remains OPEN.** V18 is finite algebra plus explicit provider interfaces.

Namespace `Erdos287.ResearchBankV18`. Aggregator `RequestProject/Erdos287/ResearchBankV18.lean`.

Semantic classes used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **OPEN**, **REPAIRED / RETIRED**.

## Files

| File | Content |
|---|---|
| `ResearchBankV18/ColourConductor.lean` | `e_D`, colour-conductor reduction without unit hypothesis on `c`; `E = 1` case |
| `ResearchBankV18/CharacterExpansion.lean` | Dirichlet-character expansion on `(ZMod n)ˣ`, monomial separation for all `m` |
| `ResearchBankV18/ReciprocalMonomial.lean` | exact decomposition of `Ω_D(h,v)` |
| `ResearchBankV18/ScalarVariation.lean` | `M_p`, `M_p³ ≤ p²`, principal Ramanujan sum, `GaussMagnitudeProvider` |
| `ResearchBankV18/ProviderInterfaces.lean` | `MaynardFirstExponentialProvider`, `MaynardSecondExponentialProvider` |
| `ResearchBankV18/PostCenteringTransfer.lean` | multiplier transfer; polarization constants 4 / 16 / 64 |
| `ResearchBankV18/NegativeControls.lean` | `D^m` residue-cell bound strictly weaker |
| `ResearchBankV18/Ledger.lean` | `v18Ledger` |
| `ResearchBankV18/AxiomAudit.lean` | `#print axioms` for all 55 V18 theorems |

## Classified results

### LEAN BANK
- `ColourConductor.colour_conductor_reduction` — `g = gcd(D,c)`, `E = D/g`, `c₀ = c/g`; for a
  unit `z`: `e_D(h c z̄) = e_E(h c₀ z̄')`. **No hypothesis that `c` is a unit mod `D`.**
  `colour_conductor_E_one` handles `E = 1`; `nonunit_fixture` (`D = 6`, `c = 4`).
- `CharacterExpansion.expansion`, `monomial_separation`, `one_family_for_all_m`, `coef_shift`.
- `ReciprocalMonomial.reciprocal_monomial_separation` —
  `Ω_D(u,v) = Σ_χ C_χ f_{0,χ}(u) Π_j f_{j,χ}(v_j)` with every `‖f‖_∞ ≤ 1`, for every number `m` of
  variables; `reciprocal_bound_by_variation` — `‖Ω_D‖ ≤ Σ_χ ‖C_χ‖`, independent of `m`.
- **V18.3 (m does not enter the exponent)**: `CharacterExpansion.one_family_for_all_m` — one
  coefficient family and one total variation serves every `m` simultaneously.
- `ScalarVariation.principal_sum` (Ramanujan sum `= −1`, from Mathlib's `ZMod.stdAddChar`),
  `principal_coef_norm`, `Mp_le_sqrt`, `Mp_sq_le`, `Mp_cube_le` (`M_p³ ≤ p²` for all `p ≥ 2`,
  exact; `Mp_two`: `M_2 = 1`), `crt_phase_split`, `prod_Mp_cube_le`
  (`(Π_{p∈S} M_p)³ ≤ E²` for squarefree `E = Π_{p∈S} p`). The bound `Σ|C_λ| ≤ E^{2/3}` is stated
  without real powers as `(Σ|C_λ|)³ ≤ E²`.
- `PostCenteringTransfer.polarize_one` (4), `polarize_two` (16), `polarize_three` (64).
- `Ledger` preservation / #287-open theorems.

### LEAN CONDITIONAL
- `ScalarVariation.local_variation_le` — from `GaussMagnitudeProvider`: local variation mod `p`
  `≤ M_p`, hence cube `≤ p²`.
- `PostCenteringTransfer.multiplier_transfer`, `multiplier_transfer_second` — if a base estimate
  is stable under arbitrary one-bounded coefficient slots and the phase has a decomposition of
  total scalar variation `M`, the coloured estimate costs at most `M ×` the provider bound.

### EXTERNAL PROVIDER
- `GaussMagnitudeProvider` — ONLY the Gauss-sum magnitude `‖C_χ‖ ≤ √p/(p−1)` for nonprincipal
  `χ` (Mathlib has `gaussSum_mul_gaussSum_eq_card` but no norm form used here).
- `MaynardFirstExponentialProvider`, `MaynardSecondExponentialProvider` — Maynard's lemmas are not
  formalized; contracts carry their real content (`first_provider_falsifiable`).

### FINITE REGRESSION
- `ColourConductor.nonunit_fixture`; `ScalarVariation.Mp_two`.

### OPEN
- That every actual branch instantiates the Maynard providers (not claimed anywhere).
- The identification of the character family mod `E` with the tensor product of local families
  (only the CRT phase split and the numerical product are formalized).

### REPAIRED / RETIRED
- The `D^m` residue-cell bound as canonical statement: `NegativeControls.residue_cell_strictly_weaker`
  (`(D^m)³ > D²` for `D ≥ 2`, `m ≥ 1`), `residue_cell_unbounded_in_m`; `E_cost_le_D_cost`.

## Trust
- 55 theorems; `#print axioms`: 49 × `[propext, Classical.choice, Quot.sound]`,
  2 × `[propext, Quot.sound]`, 1 × `[propext]`, 3 × no axioms. No other axiom.
- No forbidden token.
