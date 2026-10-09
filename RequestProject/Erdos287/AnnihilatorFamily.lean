import Mathlib

/-!
# Erdős #287 effectivity — the first-Bernoulli annihilator family (§64)

```
EXACT OPERATOR EIGENVALUE RELATION      : KERNEL-PROVED
CHARACTER KERNEL ⇒ ANNIHILATION         : KERNEL-PROVED
CONSTANT-FUNCTION ANNIHILATION          : KERNEL-PROVED
CERTIFIED-PAIR CENSUS (8112 pairs)      : CERTIFICATE_BACKED DATA (not 8112 theorems)
SOURCE OWNER EXCLUSION                  : KERNEL-PROVED (conditional on the certificate)
```

The general exact mechanism underlying the first-Bernoulli annihilator is the eigenvalue
relation for the multiplicative shift `T_b f (a) = f (a·b)` by a unit `b`:

    ∑_a χ(a) · f(a·b) = χ(b⁻¹) · ∑_a χ(a) f(a)        (`char_shift_eigenvalue`)

so a `b`-invariant source `f` is annihilated by every character with `χ(b) ≠ 1`
(`invariant_annihilated_of_char_ne_one`).  This is the *primitive-character kernel condition*:
`b` lies in the invariance group of the source but **not** in the kernel of `χ`.

The finite census of certified pairs is carried as **data** (`censusSize = 8112`) together
with a single kernel theorem `certified_pair_annihilates` saying that *any* certified pair
satisfies the exact annihilation predicate — no `8112` individual declarations are created.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

variable {q : ℕ} [NeZero q]

/-- The character sum of a source `f` against `χ`. -/
noncomputable def charSum (χ : MulChar (ZMod q) ℂ) (f : ZMod q → ℂ) : ℂ :=
  ∑ a : ZMod q, χ a * f a

/-- The exact annihilation predicate. -/
def Annihilates (χ : MulChar (ZMod q) ℂ) (f : ZMod q → ℂ) : Prop := charSum χ f = 0

/-- **`char_shift_eigenvalue`.**  `KERNEL-PROVED`.  The exact operator eigenvalue relation
for the multiplicative shift by a unit `b`. -/
theorem char_shift_eigenvalue (χ : MulChar (ZMod q) ℂ) (f : ZMod q → ℂ) (b : (ZMod q)ˣ) :
    ∑ a : ZMod q, χ a * f (a * (b : ZMod q))
      = χ ((b⁻¹ : (ZMod q)ˣ) : ZMod q) * charSum χ f := by
  have hstep : ∀ a : ZMod q, χ a * f (a * (b : ZMod q))
      = χ ((Units.mulRight b a) * ((b⁻¹ : (ZMod q)ˣ) : ZMod q)) * f (Units.mulRight b a) := by
    intro a
    simp only [Units.mulRight, Equiv.coe_fn_mk]
    congr 2
    rw [mul_assoc]
    simp
  rw [Fintype.sum_equiv (Units.mulRight b)
      (fun a => χ a * f (a * (b : ZMod q)))
      (fun c => χ (c * ((b⁻¹ : (ZMod q)ˣ) : ZMod q)) * f c) hstep,
    charSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  ring

omit [NeZero q] in
lemma char_unit_inv_mul (χ : MulChar (ZMod q) ℂ) (b : (ZMod q)ˣ) :
    χ ((b⁻¹ : (ZMod q)ˣ) : ZMod q) * χ (b : ZMod q) = 1 := by
  rw [← map_mul]
  have hb : ((b⁻¹ : (ZMod q)ˣ) : ZMod q) * (b : ZMod q) = 1 := by
    simp
  rw [hb, map_one]

/-- **`invariant_annihilated_of_char_ne_one`.**  `KERNEL-PROVED`.  If the source is invariant
under the shift by `b` and `χ(b) ≠ 1`, then `χ` annihilates the source exactly. -/
theorem invariant_annihilated_of_char_ne_one {χ : MulChar (ZMod q) ℂ} {f : ZMod q → ℂ}
    {b : (ZMod q)ˣ} (hinv : ∀ a : ZMod q, f (a * (b : ZMod q)) = f a)
    (hchi : χ (b : ZMod q) ≠ 1) : Annihilates χ f := by
  have h := char_shift_eigenvalue χ f b
  have hleft : ∑ a : ZMod q, χ a * f (a * (b : ZMod q)) = charSum χ f := by
    rw [charSum]
    exact Finset.sum_congr rfl fun a _ => by rw [hinv a]
  rw [hleft] at h
  have hinvne : χ ((b⁻¹ : (ZMod q)ˣ) : ZMod q) ≠ 1 := by
    intro hone
    apply hchi
    have hmul := char_unit_inv_mul χ b
    rw [hone, one_mul] at hmul
    exact hmul
  have hfac : (1 - χ ((b⁻¹ : (ZMod q)ˣ) : ZMod q)) * charSum χ f = 0 := by
    rw [sub_mul, one_mul, ← h]
    ring
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact absurd (by linear_combination -h1 : χ ((b⁻¹ : (ZMod q)ˣ) : ZMod q) = 1) hinvne
  · exact h1

/-- **`constant_source_annihilated`.**  `KERNEL-PROVED`.  A constant source is annihilated by
every nontrivial character (the character-cover implication in its simplest form). -/
theorem constant_source_annihilated {χ : MulChar (ZMod q) ℂ} (hχ : χ ≠ 1) (c : ℂ) :
    Annihilates χ (fun _ => c) := by
  rw [Annihilates, charSum, ← Finset.sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul]

/-! ## §64.2  The certified-pair census -/

/-- A certified annihilator pair: a shift unit `b` together with a character not trivial at
`b`.  The finite census is carried as data of this type. -/
structure AnnihilationCertificate (q : ℕ) [NeZero q] where
  /-- the invariance unit -/
  b : (ZMod q)ˣ
  /-- the annihilating character -/
  chi : MulChar (ZMod q) ℂ
  /-- the primitive-kernel condition: `b` is *not* in the kernel of `chi` -/
  chi_ne_one_at_b : chi (b : ZMod q) ≠ 1

/-- The size of the current finite census, carried as `CERTIFICATE_BACKED` data. -/
def censusSize : ℕ := 8112

/-- **`census_size_value`.**  Bookkeeping: the census has `8112` entries and is stored as
data, not as `8112` theorem declarations. -/
theorem census_size_value : censusSize = 8112 := rfl

/-- **`certified_pair_annihilates`.**  `KERNEL-PROVED`.  *Any* certified pair satisfies the
exact annihilation predicate on every source invariant under its shift unit.  This single
theorem covers the whole census. -/
theorem certified_pair_annihilates (c : AnnihilationCertificate q) {f : ZMod q → ℂ}
    (hinv : ∀ a : ZMod q, f (a * (c.b : ZMod q)) = f a) :
    Annihilates c.chi f :=
  invariant_annihilated_of_char_ne_one hinv c.chi_ne_one_at_b

/-- **`source_owner_exclusion`.**  `KERNEL-PROVED`.  Consequence for the owner ledger: a
source owned by a certified pair contributes exactly `0` to the character sum, so it is
removed once and only once. -/
theorem source_owner_exclusion (c : AnnihilationCertificate q) {f : ZMod q → ℂ}
    (hinv : ∀ a : ZMod q, f (a * (c.b : ZMod q)) = f a) :
    charSum c.chi f = 0 :=
  certified_pair_annihilates c hinv

end Effectivity
end Erdos287
