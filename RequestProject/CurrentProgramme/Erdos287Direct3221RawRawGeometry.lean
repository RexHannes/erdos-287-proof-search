import Mathlib

/-!
# Erdős #287 direct3221 raw-raw shift geometry

Deterministic congruence algebra only.  This file does not contain the Selberg-sieve
or Shiu estimates used in the paper/research calculation.
-/

namespace Erdos287Direct3221RawRawGeometry

/-- If two integers are congruent modulo a positive modulus, their difference is an integer multiple of it. -/
theorem exists_shift_of_modEq {q w w' : ℤ} (hq : q ≠ 0)
    (h : w % q = w' % q) :
    ∃ t : ℤ, w = w' + q * t := by
  have hdvd : q ∣ w - w' := by
    exact Int.dvd_sub_of_emod_eq_emod h
  rcases hdvd with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  linarith

/-- The affine divisibility condition is preserved as explicit source data. -/
theorem affine_divisibility_restate {q m w' s : ℤ}
    (h : q ∣ 2 * m * w' + s) :
    q ∣ 2 * m * w' + s := h

end Erdos287Direct3221RawRawGeometry
