import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V23 §4: the good-prime Euler factor

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

At a good prime `p` the pair `(L_i, L_j)` is a unit for exactly `n = p - 2` residues; each of
the `r` spectator forms vanishes at exactly one of them, at DISTINCT residues (`root`
injective).  With Mellin parameters `x_k = p^{-s_k}`, `y_k = p^{-t_k}` the local factor of the
signed divisor square `∏_k (1 - x_k 1_{p|L_k})(1 - y_k 1_{p|L_k})` is

    E_p(s,t) = 1 + 1/(p-2) · Σ_{k=1}^r ( p^{-s_k-t_k} - p^{-s_k} - p^{-t_k} ).

Kernel-proved (LEAN BANK):
* `prod_one_add_indicator` — distinct roots: `∏_k (1 + 1_{t=root k} c_k) = 1 + Σ_k 1_{t=root k} c_k`;
* **`local_signed_square_average`** — the finite average of the signed square equals
  `1 + (1/n) Σ_k (x_k y_k - x_k - y_k)`;
* **`eulerFactor_eq_local_average`** — `E_p(s,t)` IS that average (with `n = p - 2`);
* **`signed_square_zero_is_avoidance`** — at zero parameters the signed divisor square is the
  indicator that ALL spectator forms avoid `p`;
* **`eulerFactor_zero`** — `E_p(0,0) = (p - 2 - r)/(p - 2)` = the local probability that all
  spectator forms avoid `p`.
-/

namespace Erdos287
namespace ResearchBankV23
namespace GoodPrimeEulerFactor

open Finset

/-- The good-prime local Euler factor `E_p(s,t)`. -/
noncomputable def eulerFactor (p r : ℕ) (s t : Fin r → ℝ) : ℝ :=
  1 + 1 / ((p : ℝ) - 2) *
    ∑ k, ((p : ℝ) ^ (-(s k + t k)) - (p : ℝ) ^ (-s k) - (p : ℝ) ^ (-t k))

variable {n r : ℕ} (root : Fin r → Fin n)

/-- Distinct roots: at most one indicator is on. -/
theorem prod_one_add_indicator (hroot : Function.Injective root) (c : Fin r → ℝ) (t : Fin n) :
    ∏ k, (1 + (if t = root k then c k else 0)) = 1 + ∑ k, (if t = root k then c k else 0) := by
  by_cases h : ∃ k, t = root k
  · obtain ⟨k0, hk0⟩ := h
    have hother : ∀ k, k ≠ k0 → ¬ t = root k := by
      intro k hk ht; exact hk (hroot (ht.symm.trans hk0))
    rw [prod_eq_single k0 (fun k _ hk => by simp [hother k hk]) (by simp),
      sum_eq_single k0 (fun k _ hk => by simp [hother k hk]) (by simp)]
  · push_neg at h
    simp [h]

/-- The signed square of one spectator form. -/
def signedSq (x y : ℝ) (b : Prop) [Decidable b] : ℝ :=
  (1 - if b then x else 0) * (1 - if b then y else 0)

theorem signedSq_eq (x y : ℝ) (b : Prop) [Decidable b] :
    signedSq x y b = 1 + if b then x * y - x - y else 0 := by
  unfold signedSq; split_ifs <;> ring

/-- **Finite average of the signed divisor square.** -/
theorem local_signed_square_average (hroot : Function.Injective root) (hn : 0 < n)
    (x y : Fin r → ℝ) :
    (1 / (n : ℝ)) * ∑ t : Fin n, ∏ k, signedSq (x k) (y k) (t = root k) =
      1 + (1 / (n : ℝ)) * ∑ k, (x k * y k - x k - y k) := by
  simp_rw [signedSq_eq]
  simp_rw [prod_one_add_indicator root hroot (fun k => x k * y k - x k - y k)]
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, sum_comm]
  have : ∀ k, ∑ t : Fin n, (if t = root k then x k * y k - x k - y k else 0) =
      x k * y k - x k - y k := fun k => by simp
  simp_rw [this]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [nsmul_eq_mul]
  field_simp

/-- **The Euler factor is the local average of the signed square** (`n = p - 2`, good `p`). -/
theorem eulerFactor_eq_local_average {p : ℕ} (hp : n + 2 = p) (hroot : Function.Injective root)
    (hn : 0 < n) (s t : Fin r → ℝ) :
    eulerFactor p r s t = (1 / (n : ℝ)) * ∑ τ : Fin n,
      ∏ k, signedSq ((p : ℝ) ^ (-s k)) ((p : ℝ) ^ (-t k)) (τ = root k) := by
  rw [local_signed_square_average root hroot hn]
  unfold eulerFactor
  have hpn : (p : ℝ) - 2 = n := by rw [← hp]; push_cast; ring
  have hp0 : (0 : ℝ) < p := by rw [← hp]; positivity
  rw [hpn]
  congr 2
  refine sum_congr rfl fun k _ => ?_
  rw [neg_add, Real.rpow_add hp0]

/-- **At zero parameters the signed divisor square is the avoidance indicator.** -/
theorem signed_square_zero_is_avoidance (τ : Fin n) :
    ∏ k, signedSq 1 1 (τ = root k) = if ∀ k, τ ≠ root k then 1 else 0 := by
  by_cases h : ∀ k, τ ≠ root k
  · rw [if_pos h]; exact prod_eq_one fun k _ => by simp [signedSq, h k]
  · rw [if_neg h]; push_neg at h
    obtain ⟨k, hk⟩ := h
    exact prod_eq_zero (mem_univ k) (by simp [signedSq, hk])

/-- **`E_p(0,0)` is the local probability that all spectator forms avoid `p`.** -/
theorem eulerFactor_zero {p : ℕ} (hp : n + 2 = p) (hroot : Function.Injective root)
    (hn : 0 < n) :
    eulerFactor p r 0 0 = ((n : ℝ) - r) / n ∧
      eulerFactor p r 0 0 =
        (1 / (n : ℝ)) * ∑ τ : Fin n, (if ∀ k, τ ≠ root k then (1 : ℝ) else 0) := by
  have hav := eulerFactor_eq_local_average root hp hroot hn 0 0
  simp only [Pi.zero_apply, neg_zero, Real.rpow_zero] at hav
  simp_rw [signed_square_zero_is_avoidance] at hav
  refine ⟨?_, hav⟩
  unfold eulerFactor
  simp only [Pi.zero_apply, add_zero, neg_zero, Real.rpow_zero, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hpn : (p : ℝ) - 2 = n := by rw [← hp]; push_cast; ring
  rw [hpn]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end GoodPrimeEulerFactor
end ResearchBankV23
end Erdos287
