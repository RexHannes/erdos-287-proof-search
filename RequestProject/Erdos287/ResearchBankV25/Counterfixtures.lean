import RequestProject.Erdos287.ResearchBankV25.FixedResidueEnergy

/-!
# Erdős #287 — Research Bank V25 §3.6: counterfixtures (REPAIRED / RETIRED inference patterns)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**A. Residue restriction does not preserve a global SW statement.**  The constant sequence
`α ≡ 1` on `[1, 6]` is exactly balanced modulo `3` (`Δ_α(3, a) = 0` for every residue class),
but its restriction `α_1 = α · 1_{n ≡ 1 (3)}` to ONE fixed residue class has
`Δ_{α_1}(3, 1) = 2 − 2/2 = 1 ≠ 0`.  (`const_sequence_balanced`,
`restricted_sequence_unbalanced`, `residue_restriction_breaks_SW`.)

**B. A fixed slope can destroy unit status on a bad fixed modulus.**  With `A_i = 2`, `A_j = 3`,
`t = 8`: the prime variable `p = A_i t + 1 = 17` is a unit mod `3`, but `A_j p = 51` is NOT a
unit mod `3`; the good slope `A_i` keeps unit status (`2·17 = 34 ≡ 1`).  (`slope_destroys_unit`.)

Both historical inferences are classified **REPAIRED / RETIRED** (see `Ledger.lean`).
-/

namespace Erdos287
namespace ResearchBankV25
namespace Counterfixtures

open Finset FixedResidueEnergy

/-- A toy exact-balance (SW-type) predicate at one modulus. -/
def Balanced (q : ℕ) [NeZero q] (Ns : Finset ℕ) (α : ℕ → ℂ) : Prop :=
  ∀ a : (ZMod q)ˣ, Disc q Ns α a = 0

theorem totient_three : Nat.totient 3 = 2 := by rw [Nat.totient_prime Nat.prime_three]

theorem count_residue : ∀ a : ZMod 3, ((Finset.Icc 1 6).filter (fun n : ℕ => (n : ZMod 3) = a)).card = 2 := by
  decide

theorem count_coprime : ((Finset.Icc 1 6).filter (fun n : ℕ => Nat.Coprime n 3)).card = 4 := by
  decide

theorem count_restricted : ((Finset.Icc 1 6).filter
    (fun n : ℕ => (n : ZMod 3) = 1 ∧ Nat.Coprime n 3)).card = 2 := by
  decide

/-- **The constant sequence is exactly balanced mod 3.** -/
theorem const_sequence_balanced : Balanced 3 (Finset.Icc 1 6) (fun _ => 1) := by
  intro a
  unfold Disc
  rw [Finset.sum_boole, Finset.sum_boole, count_residue, count_coprime, totient_three]
  norm_num

/-- **Its restriction to the class `1 mod 3` is not balanced**: `Δ = 1`. -/
theorem restricted_sequence_unbalanced :
    Disc 3 (Finset.Icc 1 6) (alphaLoc (f := 3) (fun _ => 1) 1) ((1 : (ZMod 3)ˣ) : ZMod 3) = 1 := by
  unfold Disc alphaLoc
  simp only [Units.val_one]
  have h1 : (∑ n ∈ Finset.Icc (1 : ℕ) 6, if (n : ZMod 3) = 1 then
      (if (n : ZMod 3) = 1 then (1 : ℂ) else 0) else 0) = 2 := by
    simp_rw [← ite_and, and_self]
    rw [Finset.sum_boole, count_residue 1]; norm_num
  have h2 : (∑ n ∈ Finset.Icc (1 : ℕ) 6, if Nat.Coprime n 3 then
      (if (n : ZMod 3) = 1 then (1 : ℂ) else 0) else 0) = 2 := by
    simp_rw [← ite_and]
    rw [Finset.sum_boole]
    have : ((Finset.Icc (1 : ℕ) 6).filter
        (fun n : ℕ => Nat.Coprime n 3 ∧ (n : ZMod 3) = 1)).card = 2 := by decide
    rw [this]; norm_num
  rw [h1, h2, totient_three]
  norm_num

/-- **Residue restriction breaks the global balance statement** (REPAIRED / RETIRED pattern):
the constant sequence is balanced, its restriction to one residue class is not. -/
theorem residue_restriction_breaks_SW :
    Balanced 3 (Finset.Icc 1 6) (fun _ => 1) ∧
      ¬ Balanced 3 (Finset.Icc 1 6) (alphaLoc (f := 3) (fun _ => 1) 1) := by
  refine ⟨const_sequence_balanced, fun h => ?_⟩
  have := h 1
  rw [restricted_sequence_unbalanced] at this
  exact one_ne_zero this

/-- **A fixed slope destroys unit status on a bad fixed modulus** (REPAIRED / RETIRED pattern):
`A_i = 2`, `A_j = 3`, `t = 8`, `p = A_i t + 1 = 17` prime and a unit mod `3`; `A_j p = 51` is not a
unit mod `3`; `A_i p = 34` is. -/
theorem slope_destroys_unit :
    (2 * 8 + 1 = 17) ∧ Nat.Prime 17 ∧ IsUnit ((17 : ℕ) : ZMod 3) ∧
      ¬ IsUnit (((3 * 17 : ℕ)) : ZMod 3) ∧ IsUnit (((2 * 17 : ℕ)) : ZMod 3) := by
  refine ⟨rfl, by norm_num, ?_, ?_, ?_⟩
  · rw [ZMod.isUnit_iff_coprime]; decide
  · rw [ZMod.isUnit_iff_coprime]; decide
  · rw [ZMod.isUnit_iff_coprime]; decide

end Counterfixtures
end ResearchBankV25
end Erdos287
