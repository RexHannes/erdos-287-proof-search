import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters

/-!
# Erdős #287 — Research Bank V12 §5: compatible-α saving at the concrete Type-II interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Restored Type-II variables: `k ≠ 0` (an integer), `C, q₁, q₂`, `d = C·q₁·q₂`.  The detector is

  `n₁ ≡ α (mod |k|)`,   `n₂ ≡ α (mod |k|·d)`.

For fixed `n₁` the compatible classes `α (mod |k|d)` are exactly the `d` lifts
`α = (n₁ mod |k|) + |k|·j`, `0 ≤ j < d` (`mem_detectorClasses_iff`): the `n₁`-congruence fixes `α`
modulo `|k|`, leaving exactly `d` lifts.  Hence the count is `d`, **not** `|k|·d`
(`detectorClasses_card`, re-using the V10 theorem `compatibleAlpha_card_eq_d`).

Explicit fixtures with `|k| > 1` are checked by kernel `decide`; the old count `|k|·d` fails in
each (`old_count_fails_concrete`).  This is finite combinatorics, not an analytic provider.
-/

namespace Erdos287
namespace ResearchBankV12
namespace CompatibleCellsConcrete

open Finset ResearchBankV10.TypeIICompatibleCells

/-- The concrete restored Type-II interface data. -/
structure TypeIIInterface where
  k : ℤ
  C : ℕ
  q₁ : ℕ
  q₂ : ℕ
  n₁ : ℕ

namespace TypeIIInterface

variable (I : TypeIIInterface)

/-- `d = C q₁ q₂`. -/
def d : ℕ := I.C * I.q₁ * I.q₂

/-- `|k|`. -/
def K : ℕ := I.k.natAbs

/-- The compatible `α`-classes modulo `|k| d`: `α ≡ n₁ (mod |k|)`. -/
def detectorClasses : Finset ℕ := (range (I.K * I.d)).filter (fun α => α % I.K = I.n₁ % I.K)

theorem detectorClasses_eq : I.detectorClasses = compatibleAlpha I.K I.d I.n₁ := rfl

/-- **The count of compatible classes is `d`** (for `k ≠ 0`). -/
theorem detectorClasses_card (hk : I.k ≠ 0) : I.detectorClasses.card = I.d :=
  compatibleAlpha_card_eq_d (Int.natAbs_pos.2 hk) _ _

/-- **The exact logical reason**: the `n₁`-congruence fixes `α` modulo `|k|`; the compatible
classes are exactly the `d` lifts `(n₁ mod |k|) + |k| j`, `j < d`. -/
theorem mem_detectorClasses_iff (hk : I.k ≠ 0) (α : ℕ) :
    α ∈ I.detectorClasses ↔ ∃ j < I.d, α = I.n₁ % I.K + I.K * j := by
  have hK : 0 < I.K := Int.natAbs_pos.2 hk
  have hm : I.n₁ % I.K < I.K := Nat.mod_lt _ hK
  unfold detectorClasses
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨α / I.K, Nat.div_lt_of_lt_mul h1, ?_⟩
    rw [← h2]; exact (Nat.mod_add_div α I.K).symm
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, ?_⟩
    · have : I.K * j + I.K ≤ I.K * I.d := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
    · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- The lift map `j ↦ (n₁ mod |k|) + |k| j` is injective, so distinct `j < d` give distinct
classes. -/
theorem lift_injective (hk : I.k ≠ 0) {j j' : ℕ} (h : I.n₁ % I.K + I.K * j = I.n₁ % I.K + I.K * j') :
    j = j' := by
  have hK : 0 < I.K := Int.natAbs_pos.2 hk
  exact Nat.eq_of_mul_eq_mul_left hK (by omega)

/-- **The detector forces `n₂` to be compatible**: `n₂ ≡ α (mod |k| d)` and `α ≡ n₁ (mod |k|)`
give `n₂ ≡ n₁ (mod |k|)`. -/
theorem detector_n₂_compatible {α n₂ : ℕ} (hα : α % I.K = I.n₁ % I.K)
    (h2 : n₂ % (I.K * I.d) = α % (I.K * I.d)) : n₂ % I.K = I.n₁ % I.K :=
  detector_n2_determined hα h2

/-- **The old count `|k| d` is wrong whenever `|k| > 1`, `d > 0`.** -/
theorem old_count_wrong (hk : 1 < I.K) (hd : 0 < I.d) : I.detectorClasses.card ≠ I.K * I.d :=
  old_count_fails hk hd _

/-- **The saving factor is exactly `|k|`.** -/
theorem saving_factor (hk : I.k ≠ 0) (hd : 0 < I.d) :
    ((I.K * I.d : ℕ) : ℚ) / I.detectorClasses.card = I.K :=
  outer_cell_ratio (Int.natAbs_pos.2 hk) hd _

end TypeIIInterface

/-! ## Explicit fixtures with `|k| > 1` (kernel `decide`) -/

/-- `k = −3`, `C = 2`, `q₁ = 1`, `q₂ = 5` (`d = 10`), `n₁ = 7`. -/
def fixtureA : TypeIIInterface := ⟨-3, 2, 1, 5, 7⟩

/-- `k = 4`, `C = 1`, `q₁ = 3`, `q₂ = 2` (`d = 6`), `n₁ = 11`. -/
def fixtureB : TypeIIInterface := ⟨4, 1, 3, 2, 11⟩

theorem fixtureA_card : fixtureA.detectorClasses.card = 10 ∧ fixtureA.K * fixtureA.d = 30 := by
  decide

theorem fixtureB_card : fixtureB.detectorClasses.card = 6 ∧ fixtureB.K * fixtureB.d = 24 := by
  decide

/-- The explicit lifts for fixture B: `{3, 7, 11, 15, 19, 23}`. -/
theorem fixtureB_classes : fixtureB.detectorClasses = {3, 7, 11, 15, 19, 23} := by decide

/-- **Old `|k|d` alpha-count failure on the concrete fixtures.** -/
theorem old_count_fails_concrete :
    fixtureA.detectorClasses.card ≠ fixtureA.K * fixtureA.d ∧
      fixtureB.detectorClasses.card ≠ fixtureB.K * fixtureB.d := by
  decide

end CompatibleCellsConcrete
end ResearchBankV12
end Erdos287
