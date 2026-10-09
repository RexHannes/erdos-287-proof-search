import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.CompleteLCMModulus

/-!
# Erdős #287 — Research Bank V15 §B8: divisor multiplicity weights

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Finite / combinatorial part of the grouping of labelled divisor tuples `(d, e)` by their
**complete** lcm modulus `q = lcm(d_1, …, d_K, e_1, …, e_K)`:

* `pairMultiplicity S q = #{(d, e) ∈ S × S : completeModulus d e = q}`;
* `sum_group_by_modulus` — exact regrouping of a double sum over labelled pairs by `q`;
* `sum_pairMultiplicity` — the multiplicities add up to `|S|²`;
* `abs_sum_le_multiplicity` — if `|f(d,e)| ≤ B(q(d,e))` then
  `|∑_{d,e} f| ≤ ∑_q pairMultiplicity(q) · B(q)`;
* `multiplicity_fixture` — for `K = 1` and `S = divisors of 6`, exactly `9 = 3²` labelled pairs have
  complete modulus `6`.

Nothing here is a *pointwise polylogarithmic* multiplicity bound; the analytic divisor-moment /
Cauchy estimate is carried by the explicit provider `ZerothMomentContract.DivisorMomentProvider`.
-/

namespace Erdos287
namespace ResearchBankV15
namespace DivisorMultiplicity

open CompleteLCMModulus

variable {K : ℕ}

/-- The number of labelled pairs in `S × S` with complete modulus `q`. -/
def pairMultiplicity (S : Finset (Fin K → ℕ)) (q : ℕ) : ℕ :=
  ((S ×ˢ S).filter fun de => completeModulus de.1 de.2 = q).card

/-- The complete moduli that occur. -/
def moduli (S : Finset (Fin K → ℕ)) : Finset ℕ :=
  (S ×ˢ S).image fun de => completeModulus de.1 de.2

theorem mem_moduli {S : Finset (Fin K → ℕ)} {x : (Fin K → ℕ) × (Fin K → ℕ)} (hx : x ∈ S ×ˢ S) :
    completeModulus x.1 x.2 ∈ moduli S := by
  unfold moduli; exact Finset.mem_image.2 ⟨x, hx, rfl⟩

/-- **Exact regrouping by the complete modulus.** -/
theorem sum_group_by_modulus {β : Type*} [AddCommMonoid β] (S : Finset (Fin K → ℕ))
    (f : (Fin K → ℕ) → (Fin K → ℕ) → β) :
    ∑ d ∈ S, ∑ e ∈ S, f d e =
      ∑ q ∈ moduli S, ∑ de ∈ (S ×ˢ S).filter (fun de => completeModulus de.1 de.2 = q),
        f de.1 de.2 := by
  rw [Finset.sum_fiberwise_of_maps_to (fun x hx => mem_moduli hx), Finset.sum_product]

/-- The multiplicities add up to `|S|²`. -/
theorem sum_pairMultiplicity (S : Finset (Fin K → ℕ)) :
    ∑ q ∈ moduli S, pairMultiplicity S q = S.card * S.card := by
  unfold pairMultiplicity
  rw [← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (fun x hx => mem_moduli hx)).symm

/-- **Multiplicity bound**: a pointwise bound depending only on the complete modulus gives a
bound weighted by the pair multiplicities. -/
theorem abs_sum_le_multiplicity (S : Finset (Fin K → ℕ))
    (f : (Fin K → ℕ) → (Fin K → ℕ) → ℝ) (B : ℕ → ℝ)
    (hB : ∀ d ∈ S, ∀ e ∈ S, |f d e| ≤ B (completeModulus d e)) :
    |∑ d ∈ S, ∑ e ∈ S, f d e| ≤ ∑ q ∈ moduli S, (pairMultiplicity S q : ℝ) * B q := by
  rw [sum_group_by_modulus]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold pairMultiplicity
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun de hde => ?_
  obtain ⟨hmem, hq⟩ := Finset.mem_filter.1 hde
  rw [Finset.mem_product] at hmem
  rw [← hq]
  exact hB _ hmem.1 _ hmem.2

/-- Divisors of `6` as `1`-tuples. -/
def divisorTuples6 : Finset (Fin 1 → ℕ) := (Nat.divisors 6).image fun n => fun _ => n

/-- **Fixture**: exactly `9` labelled pairs of divisors of `6` have complete modulus `6`. -/
theorem multiplicity_fixture : pairMultiplicity divisorTuples6 6 = 9 := by decide

end DivisorMultiplicity
end ResearchBankV15
end Erdos287
