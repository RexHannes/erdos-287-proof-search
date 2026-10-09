import Mathlib

/-!
# Erdős #287 — Research Bank V11 §S: the exceptional-modulus firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The correct requirement: a (possible) exceptional prime factor `p_exc` must be excluded from the
**full** AP modulus `q`, **or** its exceptional-character contribution must be estimated
separately (an external estimate, a `Prop` parameter).

* `ExceptionalSafeFullModulus q pExc Sep` — `(∀ p, pExc = some p → p ∤ q) ∨ Sep`;
* `ExceptionalModulusInput pExc Sep Q` — the external input: every full modulus in `Q` is safe;
* `W_shortcut_invalid` — the incorrect shortcut "put the exceptional prime into `W` and everything
  is solved" is refuted: if `p ∣ W`, then `p` divides the full modulus `W·r`, so without the separate
  estimate the full modulus is **not** safe;
* `no_exceptional_safe` — with no exceptional prime, every modulus is safe.
-/

namespace Erdos287
namespace ResearchBankV11
namespace ExceptionalFactor

/-- The exceptional-safe full-modulus predicate. -/
def ExceptionalSafeFullModulus (q : ℕ) (pExc : Option ℕ) (Sep : Prop) : Prop :=
  (∀ p, pExc = some p → ¬ p ∣ q) ∨ Sep

/-- **External**: every full modulus of the family `Q` is exceptional-safe. -/
structure ExceptionalModulusInput (pExc : Option ℕ) (Sep : Prop) (Q : Finset ℕ) : Prop where
  safe : ∀ q ∈ Q, ExceptionalSafeFullModulus q pExc Sep

/-- With no exceptional prime, every modulus is safe. -/
theorem no_exceptional_safe (q : ℕ) (Sep : Prop) : ExceptionalSafeFullModulus q none Sep :=
  Or.inl fun _ h => by cases h

/-- Putting the exceptional prime into `W` keeps it in the full modulus `W·r`. -/
theorem exceptional_in_W_divides_full {p W : ℕ} (h : p ∣ W) (r : ℕ) : p ∣ W * r :=
  dvd_mul_of_dvd_left h r

/-- **The `W`-shortcut is invalid**: without a separate exceptional-character estimate, a full
modulus `W·r` with `p_exc ∣ W` is not exceptional-safe. -/
theorem W_shortcut_invalid {p W : ℕ} (h : p ∣ W) (r : ℕ) :
    ¬ ExceptionalSafeFullModulus (W * r) (some p) False := by
  rintro (h' | h')
  · exact h' p rfl (exceptional_in_W_divides_full h r)
  · exact h'

/-- The shortcut as a universal claim is false. -/
theorem W_shortcut_claim_false :
    ¬ ∀ p W r : ℕ, p ∣ W → ExceptionalSafeFullModulus (W * r) (some p) False :=
  fun h => W_shortcut_invalid (dvd_refl 2) 1 (h 2 2 1 (dvd_refl 2))

end ExceptionalFactor
end ResearchBankV11
end Erdos287
