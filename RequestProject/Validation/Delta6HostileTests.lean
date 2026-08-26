import Mathlib
import RequestProject.TrustedBank.Gate1A.ScaleLedger
import RequestProject.TrustedBank.Gate1A.RowConservation
import RequestProject.TrustedBank.Gate1A.AvgJDRInterface
import RequestProject.TrustedBank.Gate1B.CenteredRho
import RequestProject.TrustedBank.Gate1B.MobiusCollapse
import RequestProject.TrustedBank.Gate1B.SeparableWeights
import RequestProject.TrustedBank.Gate1B.StartInjectivity
import RequestProject.TrustedBank.R9.Certificate
import RequestProject.TrustedBank.Erdos287.GoodPrime

/-!
# Δv6 hostile tests

Every new finite theorem of this run is attacked with small examples: coprime and
non-coprime `ρ`-pairs, the repeated-prime sector, same-start versus mixed-start
injectivity, the R9 binomial identity, good-prime exclusion on genuine small reciprocal
representations, and the endpoints of the denominator span.

Where a test *fails* for the general statement, the failure is banked as a theorem
(a counterexample), and the corresponding bank theorem carries the hypothesis that
rules the failure out.  No proof is patched with an unstated assumption.
-/

open scoped BigOperators

namespace Validation
namespace Delta6

open TrustedBank

/-! ## Gate 1A: the ledger gaps -/

example : Gate1A.missingRatioExp Gate1A.V1 = 1 / 18 := Gate1A.missingRatio_V1
example : Gate1A.missingRatioExp Gate1A.V2 = 1 / 36 := Gate1A.missingRatio_V2
example : Gate1A.missingRatioExp Gate1A.V3 = 1 / 24 := Gate1A.missingRatio_V3

/-- Row mass on a two-element row index with unit vectors: the factorization is exact. -/
theorem row_mass_small_test (w : Fin 2 → ℂ) (x : Fin 1 → Fin 2 → ℂ) :
    ∑ m : Fin 1, Gate1A.massSq (Gate1A.rowVec w (x m))
      = Gate1A.massSq w * ∑ m : Fin 1, Gate1A.massSq (x m) :=
  Gate1A.total_massSq_rowVec w x

/-! ## Gate 1B: the centered ρ identity -/

example :
    Gate1B.rho (2 * 3) 6
      = Gate1B.rho 2 6 * Gate1B.rho 3 6 + (1 / (3 : ℕ) : ℚ) * Gate1B.rho 2 6
        + (1 / (2 : ℕ) : ℚ) * Gate1B.rho 3 6 := Gate1B.rho_test_2_3_6

example :
    Gate1B.rho (2 * 3) 5
      = Gate1B.rho 2 5 * Gate1B.rho 3 5 + (1 / (3 : ℕ) : ℚ) * Gate1B.rho 2 5
        + (1 / (2 : ℕ) : ℚ) * Gate1B.rho 3 5 := Gate1B.rho_test_2_3_5

/-- Non-coprime pairs break the identity (`d = p = 2`, and `d = 6`, `p = 4`). -/
example :
    Gate1B.rho (2 * 2) 2 ≠ Gate1B.rho 2 2 * Gate1B.rho 2 2
      + (1 / (2 : ℕ) : ℚ) * Gate1B.rho 2 2 + (1 / (2 : ℕ) : ℚ) * Gate1B.rho 2 2 :=
  Gate1B.rho_not_multiplicative_of_not_coprime

/-- A further coprime test with an odd square modulus `d = 9`, `p = 2`, `N = 18`. -/
theorem rho_test_9_2_18 :
    Gate1B.rho (9 * 2) 18
      = Gate1B.rho 9 18 * Gate1B.rho 2 18 + (1 / (2 : ℕ) : ℚ) * Gate1B.rho 9 18
        + (1 / (9 : ℕ) : ℚ) * Gate1B.rho 2 18 := by
  norm_num [Gate1B.rho_def]

/-! ## Gate 1B: the repeated-prime sector is excluded -/

example :
    ∃ q p : ℕ, p.Prime ∧ p ∣ q ∧ ¬ Squarefree q ∧
      ((ArithmeticFunction.moebius (q / p) : ℤ) ≠ -(ArithmeticFunction.moebius q : ℤ)) :=
  Gate1B.moebius_div_prime_fails_at_prime_square

example {p : ℕ} (hp : p.Prime) : (ArithmeticFunction.moebius (p ^ 2) : ℤ) = 0 :=
  Gate1B.moebius_prime_sq_eq_zero hp

/-! ## Gate 1B: same-start versus mixed-start -/

/-- Same-start injectivity fires on a concrete window `[3, 7)` with modulus `10`. -/
theorem sameStart_small_test {n n' : ℕ}
    (hn : n ∈ Finset.Ico 3 (3 + 4)) (hn' : n' ∈ Finset.Ico 3 (3 + 4))
    (h : (n + 5) % 10 = (n' + 5) % 10) : n = n' :=
  Gate1B.sameStart_injective (by norm_num) hn hn' h

example :
    ∃ u T a theta theta' n n' : ℕ,
      T < u ∧ n ∈ Finset.Ico a (a + T) ∧ n' ∈ Finset.Ico a (a + T) ∧ n ≠ n' ∧
        (n + theta) % u = (n' + theta') % u :=
  Gate1B.mixedStart_not_diagonal

/-! ## R9 -/

example : R9.altSum = -70 := R9.altSum_eq

/-! ## Erdős #287: good-prime exclusion on small synthetic fibres -/

open TrustedBank.Erdos287Good

/-- `A = {2,3,6}` is a genuine reciprocal representation with maximum `6`. -/
theorem synthetic_sum_six : ∑ a ∈ ({2, 3, 6} : Finset ℕ), (1 : ℚ) / a = 1 := by
  norm_num

/-- Good-prime exclusion applied to `A = {2,3,6}` at the good prime `5`. -/
theorem synthetic_exclusion_six :
    ∀ a ∈ ({2, 3, 6} : Finset ℕ), ¬ (5 : ℕ) ∣ a :=
  goodPrimeExclusion _ 6 5 goodPrime_six_five (by decide) (by decide) synthetic_sum_six

/-- `A = {2,4,6,12}` is a genuine reciprocal representation with maximum `12`. -/
theorem synthetic_sum_twelve : ∑ a ∈ ({2, 4, 6, 12} : Finset ℕ), (1 : ℚ) / a = 1 := by
  norm_num

/-- `11` is a good prime for `M = 12`. -/
theorem goodPrime_twelve_eleven : GoodPrime 12 11 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [show (12 : ℕ) / 11 = 1 from rfl, Erdos287.C_one]
  norm_num

/-- Good-prime exclusion applied to `A = {2,4,6,12}` at the good prime `11`. -/
theorem synthetic_exclusion_twelve :
    ∀ a ∈ ({2, 4, 6, 12} : Finset ℕ), ¬ (11 : ℕ) ∣ a :=
  goodPrimeExclusion _ 12 11 goodPrime_twelve_eleven (by decide) (by decide)
    synthetic_sum_twelve

/-- The criterion does not misfire: `2` is not a good prime for `M = 6`, and indeed
`2 ∣ 2 ∈ A`. -/
example : ¬ GoodPrime 6 2 := not_goodPrime_six_two

/-! ## Erdős #287: the endpoints of the denominator span -/

variable (ce : Erdos287.Gap2CE)

/-- Endpoint test (right).  The maximum `M` is a denominator, so no good prime divides
it: the adjacent-hole lemma cannot be misapplied at the right endpoint. -/
theorem goodPrime_not_dvd_max {q : ℕ} (h : GoodPrime ce.M q) : ¬ q ∣ ce.M :=
  fun hd => ce.notMem_of_excludedPP h.excludedPP hd ce.M_mem

/-- Endpoint test (left).  The minimum `N` is a denominator, so no good prime divides
it either. -/
theorem goodPrime_not_dvd_min {q : ℕ} (h : GoodPrime ce.M q) : ¬ q ∣ ce.N :=
  fun hd => ce.notMem_of_excludedPP h.excludedPP hd ce.N_mem

end Delta6
end Validation
