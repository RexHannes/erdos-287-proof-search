import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V21 §1: the finite prime-subset sieve model

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A finite prime/index set is modelled by a `Fintype P`.  A (signed) sieve is an arbitrary
coefficient function `lam : Finset P → ℝ` on squarefree moduli (= finite subsets of `P`).
**No sign condition is imposed on `lam`.**

* `divSum lam S = ∑_{A ⊆ S} lam A` — the divisor sum `a_λ(S)`;
* `numer lam q = ∑_A lam A ∏_{p ∈ A} q_p`, `denom q = ∏_p (1 - q_p)`;
* `normCost lam q = numer lam q / denom q` — the normalized sieve functional `C_λ(q)`;
* `odds q p = q_p / (1 - q_p)`.

Kernel-proved (LEAN BANK):
* `sum_supset_prod` — the finite expansion
  `∑_{D ⊇ A} ∏_{p∈D} f p ∏_{p∉D} g p = ∏_{p∈A} f p ∏_{p∉A} (f p + g p)`
  (the single combinatorial identity behind both the normalized-functional identity and the
  conditional-expectation identity of V21);
* `sum_divSum_mul` — `∑_S a_λ(S) F(S) = ∑_A λ(A) ∑_{S ⊇ A} F(S)` (exchange of summation).
-/

namespace Erdos287
namespace ResearchBankV21
namespace FiniteSieveSetup

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The divisor sum `a_λ(S) = ∑_{A ⊆ S} λ(A)`. -/
def divSum (lam : Finset P → ℝ) (S : Finset P) : ℝ := ∑ A ∈ S.powerset, lam A

/-- Numerator `∑_A λ(A) ∏_{p∈A} q_p`. -/
def numer (lam : Finset P → ℝ) (q : P → ℝ) : ℝ := ∑ A : Finset P, lam A * ∏ p ∈ A, q p

/-- Denominator `∏_p (1 - q_p)`. -/
def denom (q : P → ℝ) : ℝ := ∏ p, (1 - q p)

/-- **The normalized sieve functional** `C_λ(q) = (∑_A λ(A) ∏_{p∈A} q_p) / ∏_p (1 - q_p)`. -/
noncomputable def normCost (lam : Finset P → ℝ) (q : P → ℝ) : ℝ := numer lam q / denom q

/-- The odds `q_p / (1 - q_p)`. -/
noncomputable def odds (q : P → ℝ) (p : P) : ℝ := q p / (1 - q p)

/-- **Finite super-set expansion.** -/
theorem sum_supset_prod {R : Type*} [CommRing R] (A : Finset P) (f g : P → R) :
    ∑ D : Finset P, (if A ⊆ D then (∏ p ∈ D, f p) * ∏ p ∈ Dᶜ, g p else 0) =
      (∏ p ∈ A, f p) * ∏ p ∈ Aᶜ, (f p + g p) := by
  classical
  set g' : P → R := fun p => if p ∈ A then 0 else g p with hg'
  have hL : (∏ p ∈ A, f p) * ∏ p ∈ Aᶜ, (f p + g p) = ∏ p, (f p + g' p) := by
    rw [← Finset.prod_mul_prod_compl A (fun p => f p + g' p)]
    congr 1
    · exact Finset.prod_congr rfl fun p hp => by simp [hg', hp]
    · exact Finset.prod_congr rfl fun p hp => by
        rw [Finset.mem_compl] at hp; simp [hg', hp]
  rw [hL, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.compl_eq_univ_sdiff]
  by_cases hA : A ⊆ t
  · rw [if_pos hA]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have : p ∉ A := fun h => (Finset.mem_compl.1 hp) (hA h)
    simp [hg', this]
  · rw [if_neg hA]
    obtain ⟨p, hpA, hpt⟩ := Finset.not_subset.1 hA
    rw [Finset.prod_eq_zero (i := p) (Finset.mem_compl.2 hpt) (by simp [hg', hpA]), mul_zero]

/-- **Exchange of summation** `∑_S a_λ(S) F(S) = ∑_A λ(A) ∑_{S ⊇ A} F(S)`. -/
theorem sum_divSum_mul (lam : Finset P → ℝ) (F : Finset P → ℝ) :
    ∑ S : Finset P, divSum lam S * F S =
      ∑ A : Finset P, lam A * ∑ S : Finset P, (if A ⊆ S then F S else 0) := by
  classical
  have : ∀ S : Finset P, divSum lam S * F S =
      ∑ A : Finset P, (if A ⊆ S then lam A * F S else 0) := by
    intro S
    unfold divSum
    rw [Finset.sum_mul, ← Finset.sum_filter]
    congr 1
    ext A; simp
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

end FiniteSieveSetup
end ResearchBankV21
end Erdos287
