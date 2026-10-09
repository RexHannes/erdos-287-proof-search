# Erdős #287 — Research Bank V21 report: normalized sieve monotonicity and quadratic domination

**Erdős #287 remains OPEN.** V21 is finite algebra only. It proves no analytic statement and
claims no independence of actual primes (only independence of the finite CRT coordinates of the
principal model).

Namespace `Erdos287.ResearchBankV21`. Aggregator `RequestProject/Erdos287/ResearchBankV21.lean`.
Append-only: no V2–V20 file, no earlier report and `ARISTOTLE_SUMMARY.md` were modified.

Status labels used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **REPAIRED / RETIRED**, **OPEN**.

## Files

| File | Content |
|---|---|
| `ResearchBankV21/FiniteSieveSetup.lean` | finite prime-subset model: `divSum` (`a_λ(S) = Σ_{A⊆S} λ(A)`), `numer`, `denom`, `normCost` (`C_λ(q)`), `odds` (`q/(1-q)`), `sum_supset_prod` |
| `ResearchBankV21/NormalizedSieveMonotonicity.lean` | exact identity and monotonicity; signed-coefficient firewalls |
| `ResearchBankV21/SpectatorStates.lean` | spectator states `Y_p`, repaired local law, conditional density, envelope `h(p) = 1/(p-K+1)` |
| `ResearchBankV21/ConditionalDensity.lean` | the repaired law derived by counting residues mod `p` |
| `ResearchBankV21/QuadraticDomination.lean` | finite product model, conditional expectation, **quadratic domination** |
| `ResearchBankV21/DensityCounterfixture.lean` | mod-11 counterfixture (`4/37 ≠ 1/10`) |
| `ResearchBankV21/Ledger.lean` | `v21Ledger = v20Ledger ++ v21New`, `v21_final_status` |
| `ResearchBankV21/AxiomAudit.lean` | `#print axioms` for all 43 V21 theorems |

## Principal theorems (all LEAN BANK)

- `NormalizedSieveMonotonicity.normCost_eq_sum_divSum` — for `0 ≤ q_p < 1`,
  `C_λ(q) = (Σ_A λ(A) ∏_{p∈A} q_p) / ∏_p (1-q_p) = Σ_S a_λ(S) ∏_{p∈S} q_p/(1-q_p)`
  (finite combinatorial expansion, no probability).
- `NormalizedSieveMonotonicity.normCost_mono` — if `a_λ(S) ≥ 0` for every `S` (NOT `λ(A) ≥ 0`)
  and `0 ≤ q_p ≤ h_p < 1`, then `C_λ(q) ≤ C_λ(h)`. The hypothesis used is the divisor-sum
  nonnegativity.
- `SpectatorStates`: `stateProb_sum_one` (`P(Y=k) = 1/(p-1)`, `P(Y=0) = (p-r-1)/(p-1)`),
  `condDensity_le_envelope` (`q_p(Y) ≤ h(p) = 1/(p-r-1) = 1/(p-K+1)`, `r = K-2`), `envelope_eq`,
  `average_condDensity`, `envelope_gt_raw`.
- `ConditionalDensity.repaired_law_from_residues` — the repaired law read off from the residues.
- `QuadraticDomination.quadratic_domination` — for every spectator-state law `μ ≥ 0`, every
  conditional density `q(y) ≤ h`, every complex amplitude `B` of the spectator states:

      E[|B|² S_λ(L_j)] ≤ C_λ(h) · E[|B|² 1_sifted],

  obtained from the conditional identity `condExp_eq_normCost_mul`
  (`E[S_λ | Y] = C_λ(q(Y)) · P(sifted | Y)`) and monotonicity. `quadratic_domination_signed_tensor`
  states it for `B = Σ_e c_e φ_e` (signs inside `B` before squaring); `quadratic_domination_spectator`
  for the repaired spectator law.

## Firewalls / regressions

- **REPAIRED / RETIRED** — V17-style inference "spectator-square weighting keeps the local density
  `1/(p-1)`". Counterfixture `DensityCounterfixture.spectator_square_density_not_invariant`
  (FINITE REGRESSION): mod 11, `L_i = t+1`, `L_j = 2t+1`, `L_k = 3t+1` on `L_i ≠ 0`,
  `W = (1 - ½·1_{L_k=0})²`; weighted density of `L_j = 0` is exactly `4/37`, raw density `1/10`,
  `4/37 ≠ 1/10`. `counterfixture_within_envelope` checks the repaired envelope still dominates.
- `signed_coefficient_nonneg_divSum` (FINITE REGRESSION) — `λ({p}) = -1 < 0` while every divisor
  sum is `≥ 0`; `monotonicity_needs_divSum_nonneg` — with a negative divisor sum monotonicity fails.

## Ledger

`Ledger.v21_final_status`: normalized sieve monotonicity — LEAN BANK; spectator-conditioned quadratic
domination — LEAN BANK; V17 density-invariance shortcut — REPAIRED / RETIRED; mod-11 counterfixture —
FINITE REGRESSION; independence of actual primes — OPEN; Erdős #287 — OPEN.

## Trust

See the common trust section in `ERDOS287_RESEARCH_BANK_V24_REPORT.md` (build commands, axiom
summary, forbidden-token scan, external checker, git audit). V21: 43 theorems, all depending only on
`propext`, `Classical.choice`, `Quot.sound` (or a subset).
