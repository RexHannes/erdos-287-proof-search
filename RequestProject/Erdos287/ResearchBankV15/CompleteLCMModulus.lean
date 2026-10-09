import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V15 §B4: the complete lcm modulus

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

In the square expansion the physical modulus is the actual lcm

    q = lcm(d_1, …, d_K, e_1, …, e_K)                           (`completeModulus`).

* `squarefree_completeModulus` / `shared_primes_once` — for squarefree entries every prime
  occurs in `q` **exactly once** however many labelled coordinates it divides
  (`q.factorization p ≤ 1`);
* `dvd_completeModulus_iff` — `q ∣ n` iff every `d_i ∣ n` and every `e_i ∣ n`;
* `fixture_lcm_vs_product` — `d = (6, 10)`, `e = (15, 1)`: `q = 30` while `∏ d_i ∏ e_i = 900`;
* `firstMomentModulus i = a_i · W0 · q` — the complete AP modulus of the `i`-th first moment;
  `firstMoment_modulus_ne_q` — it is not `q` in general.
-/

namespace Erdos287
namespace ResearchBankV15
namespace CompleteLCMModulus

/-- **The complete lcm modulus** `q = lcm(d_1, …, d_K, e_1, …, e_K)`. -/
def completeModulus {K : ℕ} (d e : Fin K → ℕ) : ℕ :=
  Nat.lcm (Finset.univ.lcm d) (Finset.univ.lcm e)

theorem dvd_completeModulus_iff {K : ℕ} (d e : Fin K → ℕ) (n : ℕ) :
    completeModulus d e ∣ n ↔ (∀ i, d i ∣ n) ∧ ∀ i, e i ∣ n := by
  unfold completeModulus
  rw [Nat.lcm_dvd_iff, Finset.lcm_dvd_iff, Finset.lcm_dvd_iff]
  simp

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha0 hb0)]
  intro p
  rw [Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply]
  exact max_le ((Nat.squarefree_iff_factorization_le_one ha0).1 ha p)
    ((Nat.squarefree_iff_factorization_le_one hb0).1 hb p)

theorem squarefree_finset_lcm {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Squarefree (f i)) : Squarefree (s.lcm f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.lcm_insert]
    exact squarefree_lcm (hf j (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- For squarefree entries the complete modulus is squarefree. -/
theorem squarefree_completeModulus {K : ℕ} {d e : Fin K → ℕ} (hd : ∀ i, Squarefree (d i))
    (he : ∀ i, Squarefree (e i)) : Squarefree (completeModulus d e) :=
  squarefree_lcm (squarefree_finset_lcm _ _ fun i _ => hd i)
    (squarefree_finset_lcm _ _ fun i _ => he i)

/-- **Shared primes are counted once in `q`.** -/
theorem shared_primes_once {K : ℕ} {d e : Fin K → ℕ} (hd : ∀ i, Squarefree (d i))
    (he : ∀ i, Squarefree (e i)) (p : ℕ) : (completeModulus d e).factorization p ≤ 1 := by
  have hsq := squarefree_completeModulus hd he
  exact (Nat.squarefree_iff_factorization_le_one hsq.ne_zero).1 hsq p

/-- **Fixture**: the lcm is not the product. -/
theorem fixture_lcm_vs_product :
    completeModulus (K := 2) ![6, 10] ![15, 1] = 30 ∧
      (∏ i, (![6, 10] : Fin 2 → ℕ) i) * (∏ i, (![15, 1] : Fin 2 → ℕ) i) = 900 := by
  decide

/-- **The complete AP modulus of the `i`-th first moment**: `a_i · W0 · q`. -/
def firstMomentModulus {K : ℕ} (a : Fin K → ℕ) (W0 : ℕ) (d e : Fin K → ℕ) (i : Fin K) : ℕ :=
  a i * W0 * completeModulus d e

theorem q_dvd_firstMomentModulus {K : ℕ} (a : Fin K → ℕ) (W0 : ℕ) (d e : Fin K → ℕ)
    (i : Fin K) : completeModulus d e ∣ firstMomentModulus a W0 d e i :=
  dvd_mul_left _ _

/-- The first-moment modulus is **not** `q` in general. -/
theorem firstMoment_modulus_ne_q :
    firstMomentModulus (K := 1) ![2] 3 ![5] ![1] 0 ≠ completeModulus (K := 1) ![5] ![1] := by
  decide

end CompleteLCMModulus
end ResearchBankV15
end Erdos287
