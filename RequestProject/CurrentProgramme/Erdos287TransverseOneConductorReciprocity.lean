import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseReducedConductor

/-!
# One-conductor reciprocity — Erdős #287 (append-only)

This module is **append-only**: it edits nothing and reproves nothing.

The repaired transverse route reciprocates **only** the `q`-component of the source phase

```
e_q(A · (r m)⁻¹) · e_r(B · (q m)⁻¹),
```

producing a phase to the modulus `r m` whose `q`-dependence is `q⁻¹`, with source numerator

```
Γ = -A + m B (m mod r)⁻¹      (mod r m).
```

What is formalised here is exactly the *arithmetic* of that numerator, in two equivalent
kernel-checked shapes:

* an integer representative `Γ = -A + m B t`, where `t` is **any** integer inverse of `m` modulo
  `r` (existence is proved from `gcd(m,r) = 1`, never assumed silently), with the two congruences
  `Γ ≡ -A (mod m)` and `Γ ≡ B - A (mod r)`;
* the same two congruences in the `ZMod (r*m)` formulation, via the canonical ring maps
  `ZMod (r*m) → ZMod m` and `ZMod (r*m) → ZMod r`.

Conservatism.

* No analytic (Archimedean) transform is formalised.  §4 separates the *arithmetic phase*, which
  is a kernel theorem, from the *Archimedean factor*, which is an explicit parameter.
* Nothing here asserts that the physical source has this shape; the data `A`, `B`, `q`, `r`, `m`
  are arbitrary.
* No claim about lengths, cancellation, or closure of any branch is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseOneConductor

open Erdos287.ReciprocalUnitaryFourier

/-! ## §1  A gcd congruence helper -/

/-- **`intGcd_congr`.**  `LEAN_PROVED`.  Congruent integers have the same gcd with the modulus:
if `a ≡ b (mod n)` then `gcd(a,n) = gcd(b,n)`. -/
theorem intGcd_congr {a b n : ℤ} (h : a ≡ b [ZMOD n]) : Int.gcd a n = Int.gcd b n := by
  have hd : n ∣ a - b := Int.ModEq.dvd h.symm
  have key : ∀ u v : ℤ, n ∣ u - v → Int.gcd u n ∣ Int.gcd v n := by
    intro u v huv
    have h1 : (Int.gcd u n : ℤ) ∣ u := Int.gcd_dvd_left _ _
    have h2 : (Int.gcd u n : ℤ) ∣ n := Int.gcd_dvd_right _ _
    have h3 : (Int.gcd u n : ℤ) ∣ v := by
      have hv : v = u - (u - v) := by ring
      rw [hv]
      exact dvd_sub h1 (h2.trans huv)
    exact Int.dvd_gcd h3 h2
  exact Nat.dvd_antisymm (key a b hd) (key b a (by simpa using (dvd_neg.mpr hd)))

/-! ## §2  The modular inverse of `m` mod `r` -/

/-- **`exists_inverse_of_coprime`.**  `LEAN_PROVED`.  If `gcd(m,r) = 1` then `m` has an integer
inverse modulo `r`.  The coprimality is a hypothesis, never assumed silently. -/
theorem exists_inverse_of_coprime {r m : ℕ} (h : Nat.Coprime m r) :
    ∃ t : ℤ, (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)] := by
  have hc : IsCoprime (m : ℤ) (r : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using h)
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨u, ?_⟩
  refine Int.modEq_iff_dvd.mpr ⟨v, ?_⟩
  linarith [huv]

/-! ## §3  The source numerator `Γ` and its congruences -/

/-- The integer representative of the one-conductor source numerator,
`Γ = -A + m B t`, where `t` is an integer inverse of `m` modulo `r`. -/
def transverseGammaInt (m : ℕ) (A B t : ℤ) : ℤ := -A + (m : ℤ) * B * t

/-- **`transverseGammaInt_modEq_m`.**  `LEAN_PROVED`.  `Γ ≡ -A (mod m)`.  No hypothesis at
all is needed for this congruence. -/
theorem transverseGammaInt_modEq_m (m : ℕ) (A B t : ℤ) :
    transverseGammaInt m A B t ≡ -A [ZMOD (m : ℤ)] :=
  Int.modEq_iff_dvd.mpr ⟨-(B * t), by simp only [transverseGammaInt]; ring⟩

/-- **`transverseGammaInt_modEq_r`.**  `LEAN_PROVED`.  `Γ ≡ B - A (mod r)`, using exactly the
inverse relation `m t ≡ 1 (mod r)`. -/
theorem transverseGammaInt_modEq_r {r m : ℕ} {A B t : ℤ}
    (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) :
    transverseGammaInt m A B t ≡ B - A [ZMOD (r : ℤ)] := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ht
  refine Int.modEq_iff_dvd.mpr ⟨B * k, ?_⟩
  have hmt : (m : ℤ) * t = 1 - (r : ℤ) * k := by linarith [hk]
  simp only [transverseGammaInt]
  rw [show (-A + (m : ℤ) * B * t) = -A + B * ((m : ℤ) * t) by ring, hmt]
  ring

/-- The source numerator as an element of `ZMod (r*m)`. -/
def transverseGamma (r m : ℕ) (A B t : ℤ) : ZMod (r * m) :=
  ((transverseGammaInt m A B t : ℤ) : ZMod (r * m))

/-- **`transverseGamma_mod_m`.**  `LEAN_PROVED`.  In the `ZMod` formulation: the image of `Γ`
under the canonical map `ZMod (r*m) → ZMod m` is `-A`. -/
theorem transverseGamma_mod_m (r m : ℕ) (A B t : ℤ) :
    ZMod.castHom (dvd_mul_left m r) (ZMod m) (transverseGamma r m A B t) = -(A : ZMod m) := by
  simp only [transverseGamma, transverseGammaInt, map_intCast]
  push_cast
  simp

/-- **`transverseGamma_mod_r`.**  `LEAN_PROVED`.  In the `ZMod` formulation: the image of `Γ`
under the canonical map `ZMod (r*m) → ZMod r` is `B - A`, given `m t ≡ 1 (mod r)`. -/
theorem transverseGamma_mod_r {r m : ℕ} {A B t : ℤ} (ht : (m : ℤ) * t ≡ 1 [ZMOD (r : ℤ)]) :
    ZMod.castHom (dvd_mul_right r m) (ZMod r) (transverseGamma r m A B t)
      = (B : ZMod r) - (A : ZMod r) := by
  have h' : (((m : ℤ) * t : ℤ) : ZMod r) = ((1 : ℤ) : ZMod r) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (by exact_mod_cast ht)
  push_cast at h'
  simp only [transverseGamma, transverseGammaInt, map_intCast]
  push_cast
  rw [show (-(A : ZMod r) + (m : ZMod r) * B * t) = -(A : ZMod r) + B * ((m : ZMod r) * t) by ring,
    h']
  ring

/-! ## §4  The reduced phase interface

The research phase of the repaired route is

```
Φ_P = Arch_P · e_{m_P}(Γ^red q⁻¹).
```

The Archimedean factor `Arch_P` is **not** formalised: it enters as an explicit complex
parameter.  What is kernel-proved is the arithmetic factor. -/

/-- The reduced one-conductor phase: an explicit Archimedean parameter `Arch` times the
arithmetic phase `e_{mP}(Γ^red q⁻¹)`. -/
noncomputable def reducedPhase {mP : ℕ} [NeZero mP] (Arch : ℂ) (GammaRed q : ZMod mP) : ℂ :=
  Arch * ZMod.stdAddChar (GammaRed * q⁻¹)

/-- **`reducedPhase_norm`.**  `LEAN_PROVED`.  The arithmetic factor of the reduced phase has
modulus one, so `‖Φ_P‖ = ‖Arch_P‖`: all analytic content sits in the explicit parameter. -/
theorem reducedPhase_norm {mP : ℕ} [NeZero mP] (Arch : ℂ) (GammaRed q : ZMod mP) :
    ‖reducedPhase Arch GammaRed q‖ = ‖Arch‖ := by
  simp [reducedPhase]

/-- **`reducedPhase_arithmetic_factor`.**  `LEAN_PROVED`.  The arithmetic factor of the reduced
phase is literally the reciprocal kernel of the banked Fourier module at modulus `mP`, numerator
`Γ^red` and carrier `q`: the two descriptions agree, so the existing Fourier theorems apply
verbatim. -/
theorem reducedPhase_arithmetic_factor {mP : ℕ} [NeZero mP] (GammaRed q : ZMod mP) :
    ZMod.stdAddChar (GammaRed * q⁻¹) = unitaryFourierKernel GammaRed q⁻¹ 1 := by
  simp [unitaryFourierKernel]

/-! ## §5  Tiny finite sanity tests (not substitutes for the proofs) -/

/-- **`transverseGamma_test_r5_m3`.**  `LEAN_PROVED`.  A concrete instance: `r = 5`, `m = 3`,
`t = 2` (since `3·2 = 6 ≡ 1 mod 5`), `A = 4`, `B = 7`.  Then `Γ = -4 + 3·7·2 = 38`, and indeed
`38 ≡ -4 (mod 3)` and `38 ≡ 7 - 4 = 3 (mod 5)`. -/
theorem transverseGamma_test_r5_m3 :
    transverseGammaInt 3 4 7 2 = 38 ∧
    transverseGammaInt 3 4 7 2 ≡ -4 [ZMOD (3 : ℤ)] ∧
    transverseGammaInt 3 4 7 2 ≡ (7 : ℤ) - 4 [ZMOD (5 : ℤ)] := by
  refine ⟨by norm_num [transverseGammaInt], ?_, ?_⟩
  · exact transverseGammaInt_modEq_m 3 4 7 2
  · exact transverseGammaInt_modEq_r (r := 5) (m := 3) (by decide)

end TransverseOneConductor
end Erdos287
