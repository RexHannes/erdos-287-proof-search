import RequestProject.Erdos287.ResearchBankV21.SpectatorStates

/-!
# Erdős #287 — Research Bank V21 §4: the conditional density from residues

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A concrete residue realization of the spectator law at a good prime `p`.  The residues `t` with
`L_i(t) ≢ 0 (mod p)` form a set `Ω` of size `n = p - 1` (modelled as `Fin n`).  Each of the
`r` spectator forms vanishes at exactly one residue `root k`, the roots are distinct (`root`
injective — this is where "good prime" is used), and `L_j` vanishes at a residue `j0` that is
not a spectator root.

Kernel-proved (LEAN BANK):
* `card_state_some` — exactly one residue has `Y = some k`;
* `card_state_none` — exactly `n - r` residues have `Y = none`;
* `card_none_and_Lj`, `card_some_and_Lj` — `L_j ≡ 0` happens once inside `Y = none`, never
  inside `Y = some k`;
* `repaired_law_from_residues` — hence `Prob(Y = some k) = 1/(p-1)`,
  `Prob(Y = none) = (p-r-1)/(p-1)` and `Prob(L_j ≡ 0 | Y = none) = 1/(p-r-1)`,
  `Prob(L_j ≡ 0 | Y = some k) = 0`: exactly `stateProb` and `condDensity` of §3.
-/

namespace Erdos287
namespace ResearchBankV21
namespace ConditionalDensity

open Finset SpectatorStates

variable {n r : ℕ} (root : Fin r → Fin n) (j0 : Fin n)

theorem card_state_some (k : Fin r) : (univ.filter fun t : Fin n => t = root k).card = 1 := by
  rw [Finset.filter_eq' univ (root k)]; simp

theorem card_state_none (hroot : Function.Injective root) :
    (univ.filter fun t : Fin n => ∀ k, root k ≠ t).card = n - r := by
  have : (univ.filter fun t : Fin n => ∀ k, root k ≠ t) = univ \ univ.image root := by
    ext t; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_image_of_injective _ hroot]
  simp

theorem card_none_and_Lj (hj0 : ∀ k, root k ≠ j0) :
    (univ.filter fun t : Fin n => (∀ k, root k ≠ t) ∧ t = j0).card = 1 := by
  have : (univ.filter fun t : Fin n => (∀ k, root k ≠ t) ∧ t = j0) = {j0} := by
    ext t; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hj0, rfl⟩
  rw [this, card_singleton]

theorem card_some_and_Lj (hj0 : ∀ k, root k ≠ j0) (k : Fin r) :
    (univ.filter fun t : Fin n => t = root k ∧ t = j0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro t - ⟨rfl, h⟩
  exact hj0 k h

/-- **The repaired local law, derived from residue counting** (with `p = n + 1`). -/
theorem repaired_law_from_residues (hroot : Function.Injective root) (hj0 : ∀ k, root k ≠ j0)
    (hrn : r < n) (k : Fin r) :
    ((univ.filter fun t : Fin n => t = root k).card : ℝ) / n = stateProb (n + 1) r (some k) ∧
    ((univ.filter fun t : Fin n => ∀ k, root k ≠ t).card : ℝ) / n = stateProb (n + 1) r none ∧
    ((univ.filter fun t : Fin n => (∀ k, root k ≠ t) ∧ t = j0).card : ℝ) /
        (univ.filter fun t : Fin n => ∀ k, root k ≠ t).card = condDensity (n + 1) r none ∧
    ((univ.filter fun t : Fin n => t = root k ∧ t = j0).card : ℝ) /
        (univ.filter fun t : Fin n => t = root k).card = condDensity (n + 1) r (some k) := by
  rw [card_state_some, card_state_none root hroot, card_none_and_Lj root j0 hj0,
    card_some_and_Lj root j0 hj0]
  simp only [stateProb, condDensity, Nat.cast_add, Nat.cast_one, Nat.cast_sub hrn.le]
  refine ⟨by ring, by ring, by ring, by simp⟩

end ConditionalDensity
end ResearchBankV21
end Erdos287
