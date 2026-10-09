import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.DerivativeKernel

/-!
# Erdős #287 — Research Bank V15 §B3: the actual Möbius coefficients

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

    λ_d = (∏_i μ(d_i)) · G(log d_1 / log X, …, log d_K / log X)   if  (∏_i d_i, W0) = 1,
    λ_d = 0                                                      otherwise.

* the coefficient uses the **integrated cutoff `G`**, not the kernel `F`;
* only `(∏ d_i, W0) = 1` is imposed — **no pairwise coprimality** between labelled coordinates:
  `shared_primes_allowed` exhibits `d = (2, 2)` (coordinates sharing the prime `2`) with
  `λ_d = G(…)`, generally nonzero;
* `lam_smul` — `λ` is linear in the cutoff (used by the normalization regression, §B9);
* `lam_eq_zero_of_not_coprime`, `lam_eq_zero_of_not_squarefree`.
-/

namespace Erdos287
namespace ResearchBankV15
namespace MobiusCoefficients

open DerivativeKernel

/-- The logarithmic coordinates `(log d_i / log X)_i`. -/
noncomputable def logCoords {K : ℕ} (X : ℝ) (d : Fin K → ℕ) : Fin K → ℝ :=
  fun i => Real.log (d i) / Real.log X

open Classical in
/-- **The actual Möbius coefficient** `λ_d`. -/
noncomputable def lam {K : ℕ} (G : Kernel K) (X : ℝ) (W0 : ℕ) (d : Fin K → ℕ) : ℝ :=
  if Nat.Coprime (∏ i, d i) W0 then
    (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * G (logCoords X d)
  else 0

theorem lam_eq_zero_of_not_coprime {K : ℕ} (G : Kernel K) (X : ℝ) (W0 : ℕ) {d : Fin K → ℕ}
    (h : ¬ Nat.Coprime (∏ i, d i) W0) : lam G X W0 d = 0 := by
  unfold lam; rw [if_neg h]

theorem lam_eq_zero_of_not_squarefree {K : ℕ} (G : Kernel K) (X : ℝ) (W0 : ℕ)
    {d : Fin K → ℕ} {i : Fin K} (h : ¬ Squarefree (d i)) : lam G X W0 d = 0 := by
  unfold lam
  split_ifs
  · rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simp
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  · rfl

/-- **Linearity in the cutoff.** -/
theorem lam_smul {K : ℕ} (G : Kernel K) (c X : ℝ) (W0 : ℕ) (d : Fin K → ℕ) :
    lam (fun x => c * G x) X W0 d = c * lam G X W0 d := by
  unfold lam; split_ifs <;> ring

/-- **Shared primes between labelled coordinates are allowed** (no pairwise coprimality):
`d = (2, 2)` with `W0 = 1` has `λ_d = μ(2)^2 G(…) = G(…)`. -/
theorem shared_primes_allowed (G : Kernel 2) (X : ℝ) :
    ¬ Nat.Coprime ((fun _ : Fin 2 => 2) 0) ((fun _ : Fin 2 => 2) 1) ∧
      lam G X 1 (fun _ => 2) = G (logCoords X (fun _ => 2)) := by
  refine ⟨by decide, ?_⟩
  unfold lam
  rw [if_pos (Nat.coprime_one_right _)]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

end MobiusCoefficients
end ResearchBankV15
end Erdos287
