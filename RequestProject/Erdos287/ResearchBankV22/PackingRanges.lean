import RequestProject.Erdos287.ResearchBankV22.PositiveSieveParameters
import RequestProject.Erdos287.ResearchBankV22.CompletedPositiveWeight

/-!
# Erdős #287 — Research Bank V22 §9: packing / range ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact added budgets (FINITE REGRESSION / parameter record):

    rho = 1/1000000,   sigma = 1/19000,   eta = 1/1100.

Kernel-proved (LEAN BANK, exact rational arithmetic):
* `repaired_margins` — the four repaired margins as supplied:
  `216791/209000000 > 0`, `13/2750 > 0`, `18038791/209000000 > 0`, `38938791/209000000 > 0`;
* `margin_relations` — exact relations among the supplied margins
  (`m₄ = m₃ + 1/10`, `m₃ = m₁ + 469/5500`) — recorded, not reinterpreted;
* `support_exponent_budget` — `rho + vartheta0 = vartheta` (the completed support
  `P_E · x^{rho} · x^{vartheta0} = P_E · x^{vartheta}`, `P_E` kept explicitly);
* `rho_genuine_power` — `rho > 0` and `x^rho → ∞`: rho is a genuine polynomial exponent, NOT
  `x^{o(1)}`;
* `completed_weight_independent_of_HB_length` — `Λ_new^+` takes no Heath-Brown length
  argument: the SAME weight is used for every `N` (its valid bilinear representation — the
  colouring allocation — may depend on `N`).

Caveat: the formulas producing the four margins from (`rho`, `sigma`, `eta`) were not supplied
to this run; the margins are recorded exactly as given and only their positivity (and the exact
relations above) is certified.  Cell inflation is paid by the rounded endpoints `w(p)` inside
`ℓ_rd` (the level condition is imposed on `w`, not on `p`).
-/

namespace Erdos287
namespace ResearchBankV22
namespace PackingRanges

open PositiveSieveParameters CompletedPositiveWeight

/-- `sigma = 1/19000`. -/
def sigma : ℚ := 1 / 19000
/-- `eta = 1/1100`. -/
def eta : ℚ := 1 / 1100

/-- The four supplied repaired margins. -/
def margin1 : ℚ := 216791 / 209000000
def margin2 : ℚ := 13 / 2750
def margin3 : ℚ := 18038791 / 209000000
def margin4 : ℚ := 38938791 / 209000000

/-- **The four repaired margins are positive.** -/
theorem repaired_margins : 0 < margin1 ∧ 0 < margin2 ∧ 0 < margin3 ∧ 0 < margin4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [margin1, margin2, margin3, margin4]

theorem margin_relations : margin4 = margin3 + 1 / 10 ∧ margin3 = margin1 + 469 / 5500 := by
  constructor <;> norm_num [margin1, margin3, margin4]

theorem budgets_pos : 0 < rho ∧ 0 < sigma ∧ 0 < eta := by
  refine ⟨rho_pos, ?_, ?_⟩ <;> norm_num [sigma, eta]

/-- `rho + vartheta0 = vartheta`. -/
theorem support_exponent_budget : rho + vartheta0 = vartheta := rho_add_vartheta0

/-- rho is a genuine polynomial exponent (not `x^{o(1)}`). -/
theorem rho_genuine_power : 0 < rho ∧
    Filter.Tendsto (fun x : ℝ => x ^ ((rho : ℚ) : ℝ)) Filter.atTop Filter.atTop :=
  ⟨rho_pos, rho_exponent_not_o1⟩

/-- The completed weight does not depend on the Heath-Brown length `N`. -/
theorem completed_weight_independent_of_HB_length (E Psm Prd : Finset ℕ) (level X : ℝ)
    (w : ℕ → ℝ) (N₁ N₂ : ℕ) :
    (fun _ : ℕ => LambdaNewPlus E Psm Prd level w X) N₁ =
      (fun _ : ℕ => LambdaNewPlus E Psm Prd level w X) N₂ := rfl

end PackingRanges
end ResearchBankV22
end Erdos287
