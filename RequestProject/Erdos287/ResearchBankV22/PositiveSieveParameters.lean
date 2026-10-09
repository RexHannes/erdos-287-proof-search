import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V22 §1: exact positive-sieve parameters

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact rational parameters (FINITE REGRESSION / parameter record, all identities kernel-checked):

    vartheta  = 273/500,        rho = 1/1000000,
    vartheta0 = vartheta - rho = 545999/1000000,
    b_z       = 501/1000        (z = x^{b_z} at the provider level only),
    s0        = vartheta0 / b_z  with 1 < s0 < 3,
    nu(S)     = rho / S,        u = x^{nu},       R(S) = ⌊vartheta0 / nu(S)⌋.

The quantifier order used everywhere in V22–V24 is

    choose S  →  choose tau  →  then x → ∞,

recorded by `QuantifierOrder` (an `∀ ε, ∃ S, ∃ τ, ∃ x₀, ∀ x ≥ x₀` shape) and never reversed.

`rho_exponent_not_o1`: `x^rho → ∞` — rho is a genuine polynomial exponent, NOT `x^{o(1)}`.
-/

namespace Erdos287
namespace ResearchBankV22
namespace PositiveSieveParameters

/-- `vartheta = 273/500`. -/
def vartheta : ℚ := 273 / 500
/-- `rho = 1/1000000`. -/
def rho : ℚ := 1 / 1000000
/-- `vartheta0 = vartheta - rho`. -/
def vartheta0 : ℚ := vartheta - rho
/-- `b_z = 501/1000`. -/
def b_z : ℚ := 501 / 1000
/-- `s0 = vartheta0 / b_z`. -/
def s0 : ℚ := vartheta0 / b_z
/-- `nu(S) = rho / S`. -/
def nu (S : ℕ) : ℚ := rho / S
/-- `R(S) = ⌊vartheta0 / nu(S)⌋`, the maximal number of rough prime atoms. -/
def R (S : ℕ) : ℕ := ⌊vartheta0 / nu S⌋₊

theorem vartheta0_eq : vartheta0 = 545999 / 1000000 := by norm_num [vartheta0, vartheta, rho]

theorem rho_add_vartheta0 : rho + vartheta0 = vartheta := by
  simp only [vartheta0]; ring

theorem s0_eq : s0 = 545999 / 501000 := by norm_num [s0, vartheta0, vartheta, rho, b_z]

theorem one_lt_s0 : 1 < s0 ∧ s0 < 3 := by rw [s0_eq]; norm_num

theorem b_z_gt_half : (1 : ℚ) / 2 < b_z := by norm_num [b_z]

theorem rho_pos : 0 < rho := by norm_num [rho]

theorem nu_pos {S : ℕ} (hS : 0 < S) : 0 < nu S := by
  unfold nu; exact div_pos rho_pos (by exact_mod_cast hS)

theorem nu_le_b_z {S : ℕ} (hS : 0 < S) : nu S ≤ b_z := by
  unfold nu
  have : (1 : ℚ) ≤ S := by exact_mod_cast hS
  calc rho / S ≤ rho := div_le_self rho_pos.le this
    _ ≤ b_z := by norm_num [rho, b_z]

/-- `R(S) · nu(S) ≤ vartheta0`. -/
theorem R_mul_nu_le {S : ℕ} (hS : 0 < S) : (R S : ℚ) * nu S ≤ vartheta0 := by
  have hn := nu_pos hS
  have := Nat.floor_le (a := vartheta0 / nu S) (div_nonneg (by rw [vartheta0_eq]; norm_num) hn.le)
  unfold R
  calc (⌊vartheta0 / nu S⌋₊ : ℚ) * nu S ≤ vartheta0 / nu S * nu S :=
        mul_le_mul_of_nonneg_right this hn.le
    _ = vartheta0 := div_mul_cancel₀ _ hn.ne'

/-- **rho is a genuine polynomial exponent**: `x^rho → ∞` (it is NOT `x^{o(1)}`). -/
theorem rho_exponent_not_o1 :
    Filter.Tendsto (fun x : ℝ => x ^ ((rho : ℚ) : ℝ)) Filter.atTop Filter.atTop :=
  tendsto_rpow_atTop (by exact_mod_cast rho_pos)

/-- The quantifier order `S → tau → x` for an eventual bound `bound S τ x ≤ target + ε`. -/
def QuantifierOrder (bound : ℕ → ℝ → ℝ → ℝ) (target : ℝ) : Prop :=
  ∀ ε > 0, ∃ S : ℕ, 0 < S ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀, bound S τ x ≤ target + ε

end PositiveSieveParameters
end ResearchBankV22
end Erdos287
