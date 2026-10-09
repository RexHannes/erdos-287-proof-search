import Mathlib

/-!
# Erdős #287 — Research Bank V27 §5.5: the common Cauchy step

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The decorated sum is `W(A, Ψ) = Σ_o A(o) Σ_i Ψ(i) K(o; i)` with outer coefficients `A` and inner
coefficients `Ψ` (depending on inner variables only), and its energy is
`V(Ψ) = Σ_o |Σ_i Ψ(i) K(o; i)|²`.

**LEAN BANK.**
* `common_cauchy` — `|Σ_o A(o) X(o)|² ≤ (Σ_o w(o)) · Σ_o |X(o)|²` whenever `|A(o)|² ≤ w(o)`;
* **`decorated_cauchy`** — `|W(A,Ψ)|² ≤ mass · V(Ψ)`, `mass = Σ_o w(o)`;
* `decorated_cauchy_normalized` — with the Maynard mass bound
  `mass ≤ log^C x · N²/(Q² R² S³)`:  `|W|² ≤ log^C x · N²/(Q²R²S³) · V(Ψ)`;
* `cauchy_direction_audit` (regression) — the REVERSED inequality `mass · V ≤ |W|²` is FALSE
  (`A = (1, −1)`, `X = (1, 1)`: `|W|² = 0 < 4 = mass · V`).
-/

namespace Erdos287
namespace ResearchBankV27
namespace CommonCauchy

open Finset

/-- **Weighted Cauchy–Schwarz** (LEAN BANK). -/
theorem common_cauchy {O : Type*} (s : Finset O) (A X : O → ℂ) (w : O → ℝ)
    (hA : ∀ o ∈ s, ‖A o‖ ^ 2 ≤ w o) :
    ‖∑ o ∈ s, A o * X o‖ ^ 2 ≤ (∑ o ∈ s, w o) * ∑ o ∈ s, ‖X o‖ ^ 2 := by
  have h1 : ‖∑ o ∈ s, A o * X o‖ ≤ ∑ o ∈ s, ‖A o‖ * ‖X o‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun o _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun o => ‖A o‖) (fun o => ‖X o‖)
  have h3 : ∑ o ∈ s, ‖A o‖ ^ 2 ≤ ∑ o ∈ s, w o := Finset.sum_le_sum hA
  calc ‖∑ o ∈ s, A o * X o‖ ^ 2 ≤ (∑ o ∈ s, ‖A o‖ * ‖X o‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ o ∈ s, ‖A o‖ ^ 2) * ∑ o ∈ s, ‖X o‖ ^ 2 := h2
    _ ≤ (∑ o ∈ s, w o) * ∑ o ∈ s, ‖X o‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun _ _ => by positivity)

/-- The inner sum `X_Ψ(o) = Σ_i Ψ(i) K(o; i)`. -/
noncomputable def innerSum {O I : Type*} [Fintype I] (K : O → I → ℂ) (Ψ : I → ℂ) (o : O) : ℂ :=
  ∑ i, Ψ i * K o i

/-- The decorated sum `W(A, Ψ)`. -/
noncomputable def decoratedSum {O I : Type*} [Fintype O] [Fintype I] (A : O → ℂ) (K : O → I → ℂ)
    (Ψ : I → ℂ) : ℂ :=
  ∑ o, A o * innerSum K Ψ o

/-- The energy `V(Ψ) = Σ_o |X_Ψ(o)|²`. -/
noncomputable def energy {O I : Type*} [Fintype O] [Fintype I] (K : O → I → ℂ) (Ψ : I → ℂ) : ℝ :=
  ∑ o, ‖innerSum K Ψ o‖ ^ 2

/-- **Decorated Cauchy** (LEAN BANK): `|W(A,Ψ)|² ≤ mass · V(Ψ)`. -/
theorem decorated_cauchy {O I : Type*} [Fintype O] [Fintype I] (A : O → ℂ) (w : O → ℝ)
    (hA : ∀ o, ‖A o‖ ^ 2 ≤ w o) (K : O → I → ℂ) (Ψ : I → ℂ) :
    ‖decoratedSum A K Ψ‖ ^ 2 ≤ (∑ o, w o) * energy K Ψ :=
  common_cauchy _ _ _ _ fun o _ => hA o

/-- **Normalized decorated Cauchy** (LEAN BANK): the direction is
`|W|² ≤ log^C x · N²/(Q²R²S³) · V(Ψ)`. -/
theorem decorated_cauchy_normalized {O I : Type*} [Fintype O] [Fintype I] (A : O → ℂ)
    (w : O → ℝ) (hA : ∀ o, ‖A o‖ ^ 2 ≤ w o) (K : O → I → ℂ) (Ψ : I → ℂ)
    {logC N Q R S : ℝ} (hmass : ∑ o, w o ≤ logC * N ^ 2 / (Q ^ 2 * R ^ 2 * S ^ 3)) :
    ‖decoratedSum A K Ψ‖ ^ 2 ≤ logC * N ^ 2 / (Q ^ 2 * R ^ 2 * S ^ 3) * energy K Ψ :=
  (decorated_cauchy A w hA K Ψ).trans
    (mul_le_mul_of_nonneg_right hmass (Finset.sum_nonneg fun _ _ => by positivity))

/-- **Direction audit** (FINITE REGRESSION): the reversed Cauchy inequality fails. -/
theorem cauchy_direction_audit :
    ¬ ∀ (A X : Fin 2 → ℂ), (∀ o, ‖A o‖ ^ 2 ≤ 1) →
      (∑ _o : Fin 2, (1 : ℝ)) * ∑ o, ‖X o‖ ^ 2 ≤ ‖∑ o, A o * X o‖ ^ 2 := by
  intro h
  have := h ![1, -1] ![1, 1] (fun o => by fin_cases o <;> simp)
  simp [Fin.sum_univ_two] at this
  norm_num at this

end CommonCauchy
end ResearchBankV27
end Erdos287
