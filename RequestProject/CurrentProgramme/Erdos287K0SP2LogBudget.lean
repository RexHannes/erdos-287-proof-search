import Mathlib

/-!
# Erdős #287 K0-SP2 reassembly log-budget ledger

Pure exponent arithmetic for the post-direct3221 source reassembly.  No analytic
number theory is encoded here.
-/

namespace Erdos287K0SP2LogBudget

/-- Research-level direct Balanced7 saving after dyadic q-reassembly. -/
def baseSavingExp : ℚ := -(3/2 : ℚ)

/-- The physical target is any net exponent strictly below `-1`. -/
def targetExp : ℚ := -1

/-- Net exponent after a nonnegative bookkeeping/reassembly cost. -/
def netExp (cost : ℚ) : ℚ := baseSavingExp + cost

/-- A total reassembly cost strictly below one half preserves the physical `o(X/log X)` margin. -/
theorem closes_of_cost_lt_half {cost : ℚ} (h : cost < 1/2) :
    netExp cost < targetExp := by
  dsimp [netExp, baseSavingExp, targetExp]
  linarith

/-- At cost exactly one half the strict margin is exhausted. -/
theorem half_cost_is_boundary : netExp (1/2) = targetExp := by
  norm_num [netExp, baseSavingExp, targetExp]

/-- Any cost at least one half cannot satisfy the strict threshold by this naive ledger. -/
theorem naive_fails_of_half_le {cost : ℚ} (h : 1/2 ≤ cost) :
    ¬ netExp cost < targetExp := by
  dsimp [netExp, baseSavingExp, targetExp]
  linarith

end Erdos287K0SP2LogBudget
