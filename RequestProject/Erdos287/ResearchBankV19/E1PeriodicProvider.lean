import RequestProject.Erdos287.ResearchBankV19.PeriodicReciprocalCompletion

/-!
# Erdős #287 — Research Bank V19 §5: the E1 periodic provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `E1PeriodicProvider n V coeff A B` — the source-level E1 contract.  It names the ACTUAL
  `q`-period `V` of the branch coefficient: `V > 0`, `gcd(n, V) = 1`, the coefficient factors
  through `ZMod V`, and the complete-sum provider holds for that `V`.  Never constructed.
* `coeff_periodic` (LEAN BANK) — the coefficient is `V`-periodic;
* `e1_bound` (LEAN CONDITIONAL) — the incomplete E1 sum is bounded by
  `(B / nV) ∑_k ‖G_I(k)‖`;
* `conductor_not_period` (FINITE REGRESSION) — the primitive additive conductor `E` and the
  `q`-period `V` are different data: there is consistent period data with `E ≠ V`, so they are
  NOT identified unless separately proved.
-/

namespace Erdos287
namespace ResearchBankV19
namespace E1Periodic

open PeriodicReciprocalCompletion

/-- **The E1 periodic provider** (contract includes the actual period `V`). -/
structure E1PeriodicProvider (n V : ℕ) [NeZero n] [NeZero (n * V)] (coeff : ℤ → ℂ)
    (A : ZMod n) (B : ℝ) : Prop where
  V_pos : 0 < V
  coprime : Nat.Coprime n V
  period_witness : ∃ ω : ZMod V → ℂ, (∀ u : ℤ, coeff u = ω (u : ZMod V)) ∧
    CompleteKloostermanProvider n V ω A B

variable {n V : ℕ} [NeZero n] [NeZero (n * V)]

/-- The coefficient is `V`-periodic. -/
theorem coeff_periodic {coeff : ℤ → ℂ} {A : ZMod n} {B : ℝ}
    (P : E1PeriodicProvider n V coeff A B) (u : ℤ) : coeff (u + V) = coeff u := by
  obtain ⟨ω, hω, -⟩ := P.period_witness
  rw [hω, hω]; congr 1; push_cast; simp

/-- **The E1 bound** (conditional on the provider). -/
theorem e1_bound {coeff : ℤ → ℂ} {A : ZMod n} {B : ℝ} (P : E1PeriodicProvider n V coeff A B)
    (I : Finset ℤ) :
    ‖∑ u ∈ I, coeff u * recip A (u : ZMod n)‖ ≤
      (B / (n * V : ℕ)) * ∑ k : ZMod (n * V), ‖geom I k‖ := by
  obtain ⟨ω, hω, hK⟩ := P.period_witness
  simp_rw [hω]
  exact periodic_completion_bound ω A hK I

/-- Period data of an E1 branch: primitive additive conductor `E` and `q`-period `V`. -/
structure E1PeriodData where
  E : ℕ
  V : ℕ
  E_pos : 0 < E
  V_pos : 0 < V
  coprime : Nat.Coprime E V

/-- **The conductor is not the period.** -/
theorem conductor_not_period : ∃ d : E1PeriodData, d.E ≠ d.V :=
  ⟨⟨5, 3, by norm_num, by norm_num, by decide⟩, by decide⟩

end E1Periodic
end ResearchBankV19
end Erdos287
