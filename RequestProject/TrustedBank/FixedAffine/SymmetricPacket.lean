import Mathlib

/-!
# Trusted bank — Bank H: the symmetric `±` projection (algebraic cancellation only)

We bank the *character identity* only:

* for a multiplicative character `χ` with `χ (-1) = -1` one has `χ 1 + χ (-1) = 0`;
* consequently the contribution of an exact symmetric pair `{a, -a}` carrying equal
  weights cancels.

This is **not** an analytic saving, and it is **not** the statement that a whole source
packet projects onto the even spectrum: that would require the exact source expansion
and belongs to the interface / challenge layer.
-/

open scoped BigOperators

namespace TrustedBank
namespace SymmetricPacket

section Ring

variable {R : Type*} [CommRing R] {R' : Type*} [CommRing R']

/-- **Bank H.1 — the odd-character identity** `χ 1 + χ (-1) = 0`. -/
theorem odd_char_pair_cancel (χ : MulChar R R') (hχ : χ (-1) = -1) :
    χ 1 + χ (-1) = 0 := by
  rw [χ.map_one, hχ, add_neg_cancel]

/-- **Bank H.2 — cancellation of an exact symmetric `±` pair.**  For an odd character
`χ` and any `a`, the two values `χ a` and `χ (-a)` cancel. -/
theorem odd_char_symm_pair (χ : MulChar R R') (hχ : χ (-1) = -1) (a : R) :
    χ a + χ (-a) = 0 := by
  have : χ (-a) = χ (-1) * χ a := by
    simpa [neg_one_mul] using map_mul χ (-1) a
  rw [this, hχ]
  ring

/-- **Bank H.3 — weighted version.**  A symmetric pair `{a, -a}` carrying the *same*
weight `w` contributes nothing to an odd character sum. -/
theorem odd_char_symm_pair_weighted (χ : MulChar R R') (hχ : χ (-1) = -1) (a : R) (w : R') :
    χ a * w + χ (-a) * w = 0 := by
  rw [← add_mul, odd_char_symm_pair χ hχ a, zero_mul]

end Ring

/-- **Bank H.4 — Dirichlet instantiation.**  For an odd Dirichlet character mod `m`,
the exact symmetric `±` pair cancels. -/
theorem dirichlet_odd_symm_pair {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : χ.Odd)
    (a : ZMod m) : χ a + χ (-a) = 0 :=
  odd_char_symm_pair χ hχ a

/-- **Bank H.5 — Dirichlet instantiation, weighted form.** -/
theorem dirichlet_odd_symm_pair_weighted {m : ℕ} (χ : DirichletCharacter ℂ m) (hχ : χ.Odd)
    (a : ZMod m) (w : ℂ) : χ a * w + χ (-a) * w = 0 :=
  odd_char_symm_pair_weighted χ hχ a w

end SymmetricPacket
end TrustedBank
