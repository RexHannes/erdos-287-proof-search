import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V6: upper-gap support disjointness (kernel)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Elementary, fully kernel-proved support-disjointness for high prime rows:

* `no_shared_denominator` : for distinct primes `p ≠ q` with `p q > M`, no positive `n ≤ M` lies
  in both the `p`-row and the `q`-row;
* `rowSupport_disjoint` : the two physical row supports are disjoint finite sets;
* `rowSupport_disjoint_of_sqrt_lt` : any two distinct prime rows above `√M` have disjoint support.

**Firewall.**  `shared_support_does_not_give_independence` records that disjointness of physical
support does *not* make the row choices independent: the `no-00` neighbour coupling is a
constraint between *different* positions and survives disjointness.  Nothing here may be used to
claim independent row selection.
-/

namespace Erdos287
namespace ResearchBankV6
namespace UpperGap

open Finset

/-! ## 1.  Physical row supports -/

/-- The physical support of the prime row `p` in the window `[1, M]`: the multiples of `p`. -/
def rowSupport (M p : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun n => p ∣ n)

theorem mem_rowSupport {M p n : ℕ} : n ∈ rowSupport M p ↔ (1 ≤ n ∧ n ≤ M) ∧ p ∣ n := by
  simp [rowSupport, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-! ## 2.  The disjointness kernel -/

/-- **Support disjointness kernel.**  For distinct primes `p ≠ q` with `p q > M`, no positive
`n ≤ M` is divisible by both `p` and `q`. -/
theorem no_shared_denominator {p q M n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hM : M < p * q) (hn1 : 1 ≤ n) (hn2 : n ≤ M) (hpn : p ∣ n) (hqn : q ∣ n) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have : p * q ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpn hqn
  have hle : p * q ≤ n := Nat.le_of_dvd hn1 this
  omega

/-- The same statement as disjointness of the two physical supports. -/
theorem rowSupport_disjoint {p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hM : M < p * q) : Disjoint (rowSupport M p) (rowSupport M q) := by
  rw [Finset.disjoint_left]
  intro n hnp hnq
  rw [mem_rowSupport] at hnp hnq
  exact no_shared_denominator hp hq hpq hM hnp.1.1 hnp.1.2 hnp.2 hnq.2

/-- **High rows have disjoint support.**  Two distinct prime rows above `√M` never share a
physical denominator position in `[1, M]`. -/
theorem rowSupport_disjoint_of_sqrt_lt {p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hps : Nat.sqrt M < p) (hqs : Nat.sqrt M < q) : Disjoint (rowSupport M p) (rowSupport M q) := by
  refine rowSupport_disjoint hp hq hpq ?_
  have h : M < (Nat.sqrt M + 1) * (Nat.sqrt M + 1) := by simpa using Nat.lt_succ_sqrt M
  have : (Nat.sqrt M + 1) * (Nat.sqrt M + 1) ≤ p * q :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Consequently, for a *family* of prime rows all above `√M`, the physical supports are pairwise
disjoint. -/
theorem rowSupports_pairwiseDisjoint {M : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.sqrt M < p) :
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (rowSupport M p) (rowSupport M q) := by
  intro p hpP q hqP hpq
  exact rowSupport_disjoint_of_sqrt_lt (hP p hpP).1 (hP q hqP).1 hpq (hP p hpP).2 (hP q hqP).2

/-! ## 3.  Firewall: disjoint support ≠ independent choices -/

/-- **Firewall.**  Disjointness of the physical supports does **not** imply that the row choices
are independent.  Formally: there is a constraint `R` on a pair of Boolean choices living on
*disjoint* coordinate sets which is not the product of its own coordinate projections — each
coordinate value is individually attainable, yet not every combination is allowed. -/
theorem shared_support_does_not_give_independence :
    ∃ R : Bool → Bool → Prop,
      (∀ a : Bool, ∃ b, R a b) ∧ (∀ b : Bool, ∃ a, R a b) ∧
      ¬ (∀ a b : Bool, R a b) := by
  refine ⟨fun a b => a = b, fun a => ⟨a, rfl⟩, fun b => ⟨b, rfl⟩, ?_⟩
  intro h
  exact absurd (h true false) (by decide)

/-- The concrete form used by the bank: two rows with disjoint supports can still be coupled by a
`no-00` type neighbour condition at *different* positions, so disjointness licenses only the
statement that no *position* is shared. -/
theorem disjoint_support_conclusion_is_only_positional {M p q : ℕ}
    (h : Disjoint (rowSupport M p) (rowSupport M q)) {n : ℕ} (hn : n ∈ rowSupport M p) :
    n ∉ rowSupport M q := Finset.disjoint_left.1 h hn

end UpperGap
end ResearchBankV6
end Erdos287
