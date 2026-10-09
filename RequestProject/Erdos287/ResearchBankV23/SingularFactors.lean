import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V23 §3: singular factors and their finite cancellation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The singular factors `S_i`, `S_ij`, `S_all` enter as explicit real numbers bundled with their
nonvanishing hypotheses (`SingularData`).  The ratios `S_ij/S_i` and `S_all/S_ij` are only
formed under these hypotheses.

Kernel-proved (LEAN BANK):
* **`singular_cancellation`** — `S_i · (S_ij/S_i) · (S_all/S_ij) = S_all`;
* `ratio_chain_pos` — all ratios are positive when the factors are positive;
* `cancellation_needs_nonzero` — without `S_i ≠ 0` the "cancellation" fails (Lean's `x/0 = 0`):
  the nonzero hypotheses are load-bearing, not decoration.
-/

namespace Erdos287
namespace ResearchBankV23
namespace SingularFactors

/-- The three singular factors with explicit nonvanishing hypotheses. -/
structure SingularData where
  Si : ℝ
  Sij : ℝ
  Sall : ℝ
  Si_ne : Si ≠ 0
  Sij_ne : Sij ≠ 0

/-- **Finite cancellation** `S_i · (S_ij/S_i) · (S_all/S_ij) = S_all`. -/
theorem singular_cancellation (S : SingularData) :
    S.Si * (S.Sij / S.Si) * (S.Sall / S.Sij) = S.Sall := by
  have h1 := S.Si_ne
  have h2 := S.Sij_ne
  field_simp

theorem ratio_chain_pos (S : SingularData) (h1 : 0 < S.Si) (h2 : 0 < S.Sij)
    (h3 : 0 < S.Sall) : 0 < S.Sij / S.Si ∧ 0 < S.Sall / S.Sij :=
  ⟨div_pos h2 h1, div_pos h3 h2⟩

/-- **The nonzero hypotheses are load-bearing**: with `S_i = 0` the chain is `0 ≠ S_all`. -/
theorem cancellation_needs_nonzero :
    ∃ Si Sij Sall : ℝ, Si * (Sij / Si) * (Sall / Sij) ≠ Sall :=
  ⟨0, 1, 1, by norm_num⟩

end SingularFactors
end ResearchBankV23
end Erdos287
