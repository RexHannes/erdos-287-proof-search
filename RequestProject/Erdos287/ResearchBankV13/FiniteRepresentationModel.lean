import RequestProject.Erdos287.ResearchBankV12
import RequestProject.Erdos287.FiniteRangeExtension

/-!
# Erdős #287 — Research Bank V13 §18: the finite representation model

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

V13 uses the project's **exact** representation type `Erdos287Counterexample A` (a finite set of
integers `> 1`, at least two of them, reciprocal sum `1`, every consecutive gap `≤ 2`), i.e. the
ordered form `1 < n₁ < ⋯ < n_k = M`, `∑ 1/nᵢ = 1`, gaps `≤ 2`
(`ProblemStatement.erdos287_seq_of_no_counterexample`).  The endpoint is `M = max A`.  No
repetitions, zero denominators, unordered lists or alternative endpoint conventions are used.

* `NoCounterexampleAt M` — no exact counterexample has `max A = M`;
* `NoCounterexampleUpTo U` — `NoCounterexampleAt M` for all `M ≤ U`;
* `noCounterexampleUpTo_iff_finiteVerified` — this is exactly the V9 `FiniteVerifiedThrough U`;
* `noCounterexample_all_iff` — `∀ M, NoCounterexampleAt M` is exactly the full statement;
* `noCounterexampleUpTo_4e9` — the unconditional finite range already banked in the project
  (`no_Erdos287Counterexample_of_max_le_4e9`) in this vocabulary.
-/

namespace Erdos287
namespace ResearchBankV13
namespace FiniteRepresentationModel

/-- No exact counterexample has endpoint `M`. -/
def NoCounterexampleAt (M : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, A.max' h.nonempty ≠ M

/-- No exact counterexample has endpoint `≤ U`. -/
def NoCounterexampleUpTo (U : ℕ) : Prop := ∀ M ≤ U, NoCounterexampleAt M

/-- `NoCounterexampleUpTo U` is exactly the V9 `FiniteVerifiedThrough U`. -/
theorem noCounterexampleUpTo_iff_finiteVerified (U : ℕ) :
    NoCounterexampleUpTo U ↔ ResearchBankV9.Splice.FiniteVerifiedThrough U := by
  constructor
  · intro h A hA
    by_contra hle; push_neg at hle
    exact h _ hle A hA rfl
  · intro h M hM A hA hAM
    have := h A hA; omega

/-- `∀ M, NoCounterexampleAt M` is exactly "no exact counterexample exists". -/
theorem noCounterexample_all_iff :
    (∀ M, NoCounterexampleAt M) ↔ ∀ A : Finset ℕ, ¬ Erdos287Counterexample A := by
  constructor
  · intro h A hA; exact h _ A hA rfl
  · intro h M A hA; exact absurd hA (h A)

theorem NoCounterexampleUpTo.mono {U V : ℕ} (h : NoCounterexampleUpTo U) (hVU : V ≤ U) :
    NoCounterexampleUpTo V := fun M hM => h M (le_trans hM hVU)

/-- **The unconditional finite range already in the project**, in V13 vocabulary. -/
theorem noCounterexampleUpTo_4e9 : NoCounterexampleUpTo 4000000000 := by
  intro M hM A hA hAM
  exact no_Erdos287Counterexample_of_max_le_4e9 hA (hAM ▸ hM)

/-- Every exact counterexample has endpoint `≥ 4` (so `NoCounterexampleUpTo 3` is free). -/
theorem noCounterexampleUpTo_3 : NoCounterexampleUpTo 3 := by
  intro M hM A hA hAM
  have := hA.four_le_max; omega

/-- Denominators of an exact counterexample lie in `[1, M]`. -/
theorem mem_le_max {A : Finset ℕ} (hA : Erdos287Counterexample A) {a : ℕ} (ha : a ∈ A) :
    0 < a ∧ a ≤ A.max' hA.nonempty :=
  ⟨lt_trans Nat.zero_lt_one (hA.one_lt a ha), Finset.le_max' _ _ ha⟩

end FiniteRepresentationModel
end ResearchBankV13
end Erdos287
