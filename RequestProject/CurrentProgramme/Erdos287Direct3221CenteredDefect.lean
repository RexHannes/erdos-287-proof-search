import Mathlib

/-!
# Erdős #287 direct centered-defect finite algebra

Elementary centered raw-minus-principal identities used by the direct3221 physical route.
No analytic estimate is asserted here.
-/

namespace Erdos287Direct3221CenteredDefect

/-- Elementary centered square bound used to avoid separately estimating cross terms. -/
theorem sq_sub_le_two_sq_add_two_sq (R P : ℝ) :
    (R - P)^2 ≤ 2 * R^2 + 2 * P^2 := by
  nlinarith [sq_nonneg (R + P)]

/-- Centering is linear and therefore can be applied before later deterministic transforms. -/
theorem centered_linear (raw principal : ℝ) :
    raw - principal = raw + (-principal) := by
  ring

end Erdos287Direct3221CenteredDefect
