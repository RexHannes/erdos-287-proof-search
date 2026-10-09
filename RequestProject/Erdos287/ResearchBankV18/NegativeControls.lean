import RequestProject.Erdos287.ResearchBankV18.ScalarVariation
import RequestProject.Erdos287.ResearchBankV18.PostCenteringTransfer

/-!
# Erdős #287 — Research Bank V18 §3: negative controls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `residue_cell_strictly_weaker` (REPAIRED / RETIRED) — the earlier residue-cell bound pays
  `D^m` (one cell per residue vector of the `m` reciprocal factors).  For `D ≥ 2` and `m ≥ 1`,
  `(D^m)^3 > D^2`, i.e. `D^m > D^{2/3}`: the residue-cell bound is strictly weaker than the
  `E^{2/3}` scalar cost (`E ≤ D`), and it is NOT the canonical formal statement;
* `residue_cell_unbounded_in_m` — the residue-cell cost is unbounded in `m`, whereas the
  character-expansion cost `variation φ` is one number for all `m`
  (`CharacterExpansion.one_family_for_all_m`);
* `E_cost_le_D_cost` — `E ∣ D`, `E ≥ 1` ⟹ `E^2 ≤ D^2`: reducing the conductor never hurts.
-/

namespace Erdos287
namespace ResearchBankV18
namespace NegativeControls

/-- **The residue-cell bound is strictly weaker.** -/
theorem residue_cell_strictly_weaker {D m : ℕ} (hD : 2 ≤ D) (hm : 1 ≤ m) :
    D ^ 2 < (D ^ m) ^ 3 := by
  calc D ^ 2 < D ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    _ ≤ D ^ (3 * m) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (D ^ m) ^ 3 := by rw [← pow_mul, mul_comm]

/-- The residue-cell cost is unbounded in the number of variables. -/
theorem residue_cell_unbounded_in_m {D : ℕ} (hD : 2 ≤ D) (B : ℕ) : ∃ m, B < D ^ m :=
  ⟨B, Nat.lt_pow_self (by omega)⟩

/-- Conductor reduction never increases the cost. -/
theorem E_cost_le_D_cost {D E : ℕ} (hD : 0 < D) (hE : E ∣ D) : E ^ 2 ≤ D ^ 2 :=
  Nat.pow_le_pow_left (Nat.le_of_dvd hD hE) 2

end NegativeControls
end ResearchBankV18
end Erdos287
