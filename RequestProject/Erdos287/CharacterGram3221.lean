import Mathlib
import RequestProject.Erdos287.HighConductorVariance3221

/-!
# V19, Phase H — the character expansion socket and the five-box factorisation

`3221-CHARACTER-ORTHOGONALITY-PROJECTION45 : PROVED_FINITE`
`3221-CHARACTER-GRAM-EXPANSION45 : PROVED_FINITE`
`3221-FIVEBOX-CHARACTER-FACTORISATION45 : PROVED_FINITE`

Dirichlet-character definitions, the conductor, and the full orthogonality relation are all
available, so the low/high conductor projection is **defined literally** and the projection
equality is **proved**, not postulated: no free `Prop` placeholder and no invented character
theory appear anywhere.

## Contents

* `cHat` — the finite character transform `ĉ_q(χ) = ∑_w c(w) χ(w)`.
* `totient_mul_residueSum_eq_sum_char` — the exact orthogonality expansion
  `φ(q) · C_q(a) = ∑_χ χ(a⁻¹) ĉ_q(χ)` for a unit residue `a`.
* `lowSet`, `highSet`, `cLow`, `cHigh` — the literal conductor projections at cutoff `D`,
  and `residueSum_eq_cLow_add_cHigh`, the exact splitting `C_q = C_q^{≤D} + C_q^{>D}`.
* `gram_expansion` — the exact Gram identity for a finite family.
* `highResidue_energy_gram` — the exact `m`-Gram expansion of the high-conductor square,
  and `inverseSampled_highResidue_gram`, its substitution at the inverse sampling point
  `a = −s (2m)⁻¹`.
* `cHat_fiveBox_factorisation`, `cHat_twoBox_factorisation` — the exact factorisation of
  the character transform over a labelled product box (`1+2+2+2`, and the two-prime
  convolutions inside a pair block).

**No character-sum bound is proved, assumed, or implied.**  Every statement here is a
finite algebraic identity.  Erdős #287 remains OPEN; Balanced7 remains OPEN.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open scoped Classical

namespace Erdos287
namespace CharGram3221

/-! ## §15a. The finite character transform and orthogonality -/

/-- The finite character transform `ĉ_q(χ) = ∑_{w ∈ Wbox} c(w) χ(w)`. -/
noncomputable def cHat (q : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (chi : DirichletCharacter ℂ q) : ℂ :=
  ∑ w ∈ Wbox, c w * chi ((w : ZMod q))

/-- **The exact orthogonality expansion.**  `PROVED_FINITE`.

For a unit residue `a` modulo `q`,

`φ(q) · C_q(a) = ∑_{χ mod q} χ(a⁻¹) ĉ_q(χ)`. -/
theorem totient_mul_residueSum_eq_sum_char {q : ℕ} [NeZero q] (Wbox : Finset ℤ) (c : ℤ → ℂ)
    {a : ZMod q} (ha : IsUnit a) :
    (q.totient : ℂ) * Erdos287.HighCond3221.residueSum q Wbox c a
      = ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * cHat q Wbox c chi := by
  have h1 : ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * cHat q Wbox c chi
      = ∑ w ∈ Wbox, c w * ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * chi ((w : ZMod q)) := by
    simp only [cHat, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun chi _ => by ring
  rw [h1]
  simp only [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  rw [Erdos287.HighCond3221.residueSum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : ((w : ZMod q)) = a
  · simp [h, mul_comm]
  · have h' : ¬ (a = ((w : ZMod q))) := fun hc => h hc.symm
    simp [h, h']

/-! ## §15b. The literal low/high conductor projection -/

/-- The characters of conductor at most `D`. -/
noncomputable def lowSet (q D : ℕ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun chi => chi.conductor ≤ D)

/-- The characters of conductor above `D`. -/
noncomputable def highSet (q D : ℕ) : Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (fun chi => ¬ chi.conductor ≤ D)

/-- The low-conductor projection `C_q^{≤D}`. -/
noncomputable def cLow (q D : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ) (a : ZMod q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi ∈ lowSet q D, chi a⁻¹ * cHat q Wbox c chi

/-- The high-conductor projection `C_q^{>D}`. -/
noncomputable def cHigh (q D : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ) (a : ZMod q) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ chi ∈ highSet q D, chi a⁻¹ * cHat q Wbox c chi

/-- **The literal projection equality.**  `PROVED_FINITE`.

`C_q(a) = C_q^{≤D}(a) + C_q^{>D}(a)` for every unit residue `a`. -/
theorem residueSum_eq_cLow_add_cHigh {q : ℕ} [NeZero q] (D : ℕ) (Wbox : Finset ℤ)
    (c : ℤ → ℂ) {a : ZMod q} (ha : IsUnit a) :
    Erdos287.HighCond3221.residueSum q Wbox c a
      = cLow q D Wbox c a + cHigh q D Wbox c a := by
  have htot : (q.totient : ℂ) ≠ 0 := by
    have : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this.ne'
  have hsplit :
      (∑ chi ∈ lowSet q D, chi a⁻¹ * cHat q Wbox c chi)
        + (∑ chi ∈ highSet q D, chi a⁻¹ * cHat q Wbox c chi)
      = ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ * cHat q Wbox c chi := by
    rw [lowSet, highSet]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [cLow, cHigh, ← mul_add, hsplit, ← totient_mul_residueSum_eq_sum_char Wbox c ha,
    ← mul_assoc, inv_mul_cancel₀ htot, one_mul]

/-! ## §15c. The exact Gram expansion -/

/-- **The exact Gram identity for a finite family.**  `PROVED_ALGEBRAIC`. -/
theorem gram_expansion {ι κ : Type*} (Ms : Finset ι) (T : Finset κ) (F : κ → ι → ℂ) :
    ∑ m ∈ Ms, (∑ chi ∈ T, F chi m) * (starRingEnd ℂ) (∑ psi ∈ T, F psi m)
      = ∑ chi ∈ T, ∑ psi ∈ T, ∑ m ∈ Ms, F chi m * (starRingEnd ℂ) (F psi m) := by
  have hstep : ∀ m ∈ Ms, (∑ chi ∈ T, F chi m) * (starRingEnd ℂ) (∑ psi ∈ T, F psi m)
      = ∑ chi ∈ T, ∑ psi ∈ T, F chi m * (starRingEnd ℂ) (F psi m) := by
    intro m _
    rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun chi _ => Finset.sum_comm

/-- The `m`-Gram factor `G_M(χ, ψ) = ∑_m χ(a_m⁻¹) conj(ψ(a_m⁻¹))`. -/
noncomputable def GM (q : ℕ) (Ms : Finset ℕ) (pt : ℕ → ZMod q)
    (chi psi : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ Ms, chi (pt m)⁻¹ * (starRingEnd ℂ) (psi (pt m)⁻¹)

/-- **`highResidue_energy_gram`.**  `PROVED_FINITE`.

The exact `m`-Gram expansion of the high-conductor square:

`∑_m |C_q^{>D}(a_m)|² = φ(q)^{-2} ∑_{χ,ψ high} ĉ(χ) conj(ĉ(ψ)) G_M(χ, ψ)`.

**This is an identity, not an estimate.** -/
theorem highResidue_energy_gram {q : ℕ} (D : ℕ) (Wbox : Finset ℤ) (c : ℤ → ℂ)
    (Ms : Finset ℕ) (pt : ℕ → ZMod q) :
    ∑ m ∈ Ms, cHigh q D Wbox c (pt m) * (starRingEnd ℂ) (cHigh q D Wbox c (pt m))
      = (q.totient : ℂ)⁻¹ ^ 2 * ∑ chi ∈ highSet q D, ∑ psi ∈ highSet q D,
          cHat q Wbox c chi * (starRingEnd ℂ) (cHat q Wbox c psi) * GM q Ms pt chi psi := by
  have hct : (starRingEnd ℂ) ((q.totient : ℂ)⁻¹) = (q.totient : ℂ)⁻¹ := by
    rw [map_inv₀]; norm_num
  have hstep : ∀ m ∈ Ms,
      cHigh q D Wbox c (pt m) * (starRingEnd ℂ) (cHigh q D Wbox c (pt m))
        = (q.totient : ℂ)⁻¹ ^ 2 *
            ((∑ chi ∈ highSet q D, chi (pt m)⁻¹ * cHat q Wbox c chi) *
              (starRingEnd ℂ) (∑ psi ∈ highSet q D, psi (pt m)⁻¹ * cHat q Wbox c psi)) := by
    intro m _
    rw [cHigh, map_mul, hct]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum,
    gram_expansion Ms (highSet q D) (fun chi m => chi (pt m)⁻¹ * cHat q Wbox c chi)]
  congr 1
  refine Finset.sum_congr rfl fun chi _ => Finset.sum_congr rfl fun psi _ => ?_
  rw [GM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  ring

/-- **The inverse-sampled substitution.**  `PROVED_FINITE`.

The same identity with `a = −s (2m)⁻¹`, i.e. at the inverse sampling point of the
high-conductor variance socket. -/
theorem inverseSampled_highResidue_gram
    (Dat : Erdos287.HighCond3221.InverseSampledHighCond3221Data) {q : ℕ} (D : ℕ)
    (Wbox : Finset ℤ) (c : ℤ → ℂ) :
    ∑ m ∈ Dat.Mbox, cHigh q D Wbox c (Dat.samplePoint q m) *
        (starRingEnd ℂ) (cHigh q D Wbox c (Dat.samplePoint q m))
      = (q.totient : ℂ)⁻¹ ^ 2 * ∑ chi ∈ highSet q D, ∑ psi ∈ highSet q D,
          cHat q Wbox c chi * (starRingEnd ℂ) (cHat q Wbox c psi) *
            GM q Dat.Mbox (fun m => Dat.samplePoint q m) chi psi :=
  highResidue_energy_gram D Wbox c Dat.Mbox (fun m => Dat.samplePoint q m)

/-! ## §16. The five-box character factorisation

The labelled `1+2+2+2` source is supported on a product box, and a Dirichlet character is
multiplicative, so its character transform factorises **exactly**.  No bound is claimed for
any of the five factors. -/

/-- A four-fold product of finite sums expands exactly into the four-fold nested sum. -/
theorem sum_mul_sum4 {i1 i2 i3 i4 : Type*} (s1 : Finset i1) (s2 : Finset i2)
    (s3 : Finset i3) (s4 : Finset i4) (f1 : i1 → ℂ) (f2 : i2 → ℂ) (f3 : i3 → ℂ)
    (f4 : i4 → ℂ) :
    (∑ i ∈ s1, f1 i) * (∑ j ∈ s2, f2 j) * (∑ k ∈ s3, f3 k) * (∑ l ∈ s4, f4 l)
      = ∑ i ∈ s1, ∑ j ∈ s2, ∑ k ∈ s3, ∑ l ∈ s4, f1 i * f2 j * f3 k * f4 l := by
  have h1 : (∑ k ∈ s3, f3 k) * (∑ l ∈ s4, f4 l) = ∑ k ∈ s3, ∑ l ∈ s4, f3 k * f4 l :=
    Finset.sum_mul_sum _ _ _ _
  have h2 : (∑ j ∈ s2, f2 j) * (∑ k ∈ s3, ∑ l ∈ s4, f3 k * f4 l)
      = ∑ j ∈ s2, ∑ k ∈ s3, ∑ l ∈ s4, f2 j * (f3 k * f4 l) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  have h3 : (∑ i ∈ s1, f1 i) * (∑ j ∈ s2, ∑ k ∈ s3, ∑ l ∈ s4, f2 j * (f3 k * f4 l))
      = ∑ i ∈ s1, ∑ j ∈ s2, ∑ k ∈ s3, ∑ l ∈ s4, f1 i * (f2 j * (f3 k * f4 l)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  rw [show (∑ i ∈ s1, f1 i) * (∑ j ∈ s2, f2 j) * (∑ k ∈ s3, f3 k) * (∑ l ∈ s4, f4 l)
      = (∑ i ∈ s1, f1 i) * ((∑ j ∈ s2, f2 j) * ((∑ k ∈ s3, f3 k) * (∑ l ∈ s4, f4 l))) by ring,
    h1, h2, h3]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **`cHat_twoBox_factorisation`.**  `PROVED_FINITE`.

The two-prime convolution inside a pair block factorises exactly under the character
transform. -/
theorem cHat_twoBox_factorisation {q : ℕ} (chi : DirichletCharacter ℂ q)
    (P1 P2 : Finset ℕ) (om1 om2 : ℕ → ℂ) :
    ∑ p ∈ P1, ∑ r ∈ P2, om1 p * om2 r * chi ((p * r : ℕ) : ZMod q)
      = (∑ p ∈ P1, om1 p * chi ((p : ℕ) : ZMod q))
        * (∑ r ∈ P2, om2 r * chi ((r : ℕ) : ZMod q)) := by
  have hmul : ∀ p r : ℕ, chi ((p * r : ℕ) : ZMod q)
      = chi ((p : ℕ) : ZMod q) * chi ((r : ℕ) : ZMod q) := by
    intro p r
    push_cast
    rw [map_mul]
  calc ∑ p ∈ P1, ∑ r ∈ P2, om1 p * om2 r * chi ((p * r : ℕ) : ZMod q)
      = ∑ p ∈ P1, (om1 p * chi ((p : ℕ) : ZMod q)) *
          ∑ r ∈ P2, om2 r * chi ((r : ℕ) : ZMod q) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hmul]; ring
    _ = (∑ p ∈ P1, om1 p * chi ((p : ℕ) : ZMod q))
          * (∑ r ∈ P2, om2 r * chi ((r : ℕ) : ZMod q)) := by
        rw [← Finset.sum_mul]

/-- **`cHat_fiveBox_factorisation`.**  `PROVED_FINITE`.

The labelled `1+2+2+2` product box: `e · a · b · c` with independent coefficients.  The
character transform factorises into the four block transforms exactly. -/
theorem cHat_fiveBox_factorisation {q : ℕ} (chi : DirichletCharacter ℂ q)
    (Ebox Abox Bbox Cbox : Finset ℕ) (eta alpha beta gamma : ℕ → ℂ) :
    ∑ e ∈ Ebox, ∑ a ∈ Abox, ∑ b ∈ Bbox, ∑ cc ∈ Cbox,
        eta e * alpha a * beta b * gamma cc * chi ((e * a * b * cc : ℕ) : ZMod q)
      = (∑ e ∈ Ebox, eta e * chi ((e : ℕ) : ZMod q))
        * (∑ a ∈ Abox, alpha a * chi ((a : ℕ) : ZMod q))
        * (∑ b ∈ Bbox, beta b * chi ((b : ℕ) : ZMod q))
        * (∑ cc ∈ Cbox, gamma cc * chi ((cc : ℕ) : ZMod q)) := by
  have hmul : ∀ e a b cc : ℕ, chi ((e * a * b * cc : ℕ) : ZMod q)
      = chi ((e : ℕ) : ZMod q) * chi ((a : ℕ) : ZMod q) * chi ((b : ℕ) : ZMod q)
        * chi ((cc : ℕ) : ZMod q) := by
    intro e a b cc
    push_cast
    rw [map_mul, map_mul, map_mul]
  rw [sum_mul_sum4]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun cc _ => by
      rw [hmul]; ring

end CharGram3221
end Erdos287
