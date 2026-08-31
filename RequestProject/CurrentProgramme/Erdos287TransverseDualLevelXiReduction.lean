import Mathlib
import RequestProject.CurrentProgramme.Erdos287TransverseDualLevelReciprocity

/-!
# Dual-level `Ξ` reduction — Erdős #287 (append-only)

This module is **append-only**.  It formalises, in exact natural/integer arithmetic:

* the **constant** `Ξ`-gcd `d_const = gcd(C_{mqg} - k_g, A_m, m q)`, its divisibility of every
  `Ξ(ℓ)`, and the reduced modulus `M₀^dual = m q / d_const` (division only after the exact
  divisibility is proved);
* the reduced affine coordinate `Ξ₀(ℓ)` with `Ξ₀(ℓ) · d_const = Ξ(ℓ)`;
* the **variable** `Ξ`-gcd `d_Ξ(ℓ) = gcd(Ξ₀(ℓ), M₀^dual)`, the twice-reduced modulus
  `M' = M₀^dual / d_Ξ` and the coprimality `gcd(Ξ'(ℓ), M') = 1`;
* the unconditional residue-uniqueness statement: for a divisor `d` of the reduced modulus with
  invertible affine slope, `d ∣ Ξ₀(ℓ)` places `ℓ` in **one** residue class mod `d`;
* an explicit interface `XiGcdTailBound` for the source-weighted large-gcd tail.  The weighted
  tail is **not** derived from residue uniqueness; the interface is proved non-automatic.

A kernel-checked separation theorem records that the constant gcd and the variable gcd are
different objects and are never conflated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseDualXi

open Erdos287.TransverseDualLevel
open Erdos287.TransverseBezoutRow

/-! ## §1  The constant `Ξ`-gcd -/

/-- The constant `Ξ`-gcd `d_const = gcd(C - k_g, A_m, m q)`, in exact `ℕ` form. -/
def dConst (mq : ℕ) (C kg Am : ℤ) : ℕ := Nat.gcd (Nat.gcd (C - kg).natAbs Am.natAbs) mq

/-- **`dConst_dvd_mq`.**  `LEAN_PROVED`. -/
theorem dConst_dvd_mq (mq : ℕ) (C kg Am : ℤ) : dConst mq C kg Am ∣ mq :=
  Nat.gcd_dvd_right _ _

/-- **`dConst_pos`.**  `LEAN_PROVED`.  Positive as soon as the modulus is. -/
theorem dConst_pos {mq : ℕ} (h : 0 < mq) (C kg Am : ℤ) : 0 < dConst mq C kg Am :=
  Nat.gcd_pos_of_pos_right _ h

/-- **`dConst_dvd_const`.**  `LEAN_PROVED`.  `d_const ∣ C - k_g`. -/
theorem dConst_dvd_const (mq : ℕ) (C kg Am : ℤ) : (dConst mq C kg Am : ℤ) ∣ (C - kg) := by
  have h : dConst mq C kg Am ∣ (C - kg).natAbs :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)

/-- **`dConst_dvd_slope`.**  `LEAN_PROVED`.  `d_const ∣ A_m`. -/
theorem dConst_dvd_slope (mq : ℕ) (C kg Am : ℤ) : (dConst mq C kg Am : ℤ) ∣ Am := by
  have h : dConst mq C kg Am ∣ Am.natAbs :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)

/-- **`dConst_dvd_Xi`.**  `LEAN_PROVED`.  The constant gcd divides **every** value of `Ξ`. -/
theorem dConst_dvd_Xi (mq : ℕ) (C kg Am ell : ℤ) :
    (dConst mq C kg Am : ℤ) ∣ Xi C kg Am ell := by
  have h1 := dConst_dvd_const mq C kg Am
  have h2 := (dConst_dvd_slope mq C kg Am).mul_right ell
  have : Xi C kg Am ell = (C - kg) - Am * ell := by unfold Xi; ring
  rw [this]
  exact dvd_sub h1 h2

/-! ## §2  The reduced modulus and the reduced coordinate -/

/-- The reduced dual modulus `M₀^dual = m q / d_const`.  The division is exact by
`dConst_dvd_mq`. -/
def M0Dual (mq : ℕ) (C kg Am : ℤ) : ℕ := mq / dConst mq C kg Am

/-- **`M0Dual_mul_dConst`.**  `LEAN_PROVED`.  The exact factorisation
`M₀^dual · d_const = m q`; no unproved division occurs. -/
theorem M0Dual_mul_dConst (mq : ℕ) (C kg Am : ℤ) :
    M0Dual mq C kg Am * dConst mq C kg Am = mq :=
  Nat.div_mul_cancel (dConst_dvd_mq mq C kg Am)

/-- **`M0Dual_pos`.**  `LEAN_PROVED`. -/
theorem M0Dual_pos {mq : ℕ} (h : 0 < mq) (C kg Am : ℤ) : 0 < M0Dual mq C kg Am :=
  Nat.div_pos (Nat.le_of_dvd h (dConst_dvd_mq mq C kg Am)) (dConst_pos h C kg Am)

/-- The reduced constant `c₀ = (C - k_g)/d_const`. -/
def c0 (mq : ℕ) (C kg Am : ℤ) : ℤ := (C - kg) / (dConst mq C kg Am : ℤ)

/-- The reduced slope `s₀ = A_m/d_const`. -/
def s0 (mq : ℕ) (C kg Am : ℤ) : ℤ := Am / (dConst mq C kg Am : ℤ)

/-- The reduced affine coordinate `Ξ₀(ℓ) = c₀ - s₀ ℓ`. -/
def Xi0 (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) : ℤ := c0 mq C kg Am - s0 mq C kg Am * ell

/-- **`Xi0_mul_dConst`.**  `LEAN_PROVED`.  The exact reduction identity
`Ξ₀(ℓ) · d_const = Ξ(ℓ)`. -/
theorem Xi0_mul_dConst {mq : ℕ} (h : 0 < mq) (C kg Am ell : ℤ) :
    Xi0 mq C kg Am ell * (dConst mq C kg Am : ℤ) = Xi C kg Am ell := by
  have hd : (dConst mq C kg Am : ℤ) ≠ 0 := by
    exact_mod_cast (dConst_pos h C kg Am).ne'
  have h1 : c0 mq C kg Am * (dConst mq C kg Am : ℤ) = C - kg :=
    Int.ediv_mul_cancel (dConst_dvd_const mq C kg Am)
  have h2 : s0 mq C kg Am * (dConst mq C kg Am : ℤ) = Am :=
    Int.ediv_mul_cancel (dConst_dvd_slope mq C kg Am)
  calc Xi0 mq C kg Am ell * (dConst mq C kg Am : ℤ)
      = c0 mq C kg Am * (dConst mq C kg Am : ℤ)
        - (s0 mq C kg Am * (dConst mq C kg Am : ℤ)) * ell := by unfold Xi0; ring
    _ = (C - kg) - Am * ell := by rw [h1, h2]
    _ = Xi C kg Am ell := by unfold Xi; ring

/-- **`Xi0_affine_slope`.**  `LEAN_PROVED`.  The reduced coordinate is affine with exact slope
`-s₀`. -/
theorem Xi0_affine_slope (mq : ℕ) (C kg Am ell : ℤ) :
    Xi0 mq C kg Am (ell + 1) - Xi0 mq C kg Am ell = -s0 mq C kg Am := by
  unfold Xi0; ring

/-! ## §3  Variable `Ξ`-gcd, reduced modulus and coprimality -/

/-- The variable `Ξ`-gcd `d_Ξ(ℓ) = gcd(Ξ₀(ℓ), M₀^dual)`. -/
def dXi (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) : ℕ :=
  Nat.gcd (Xi0 mq C kg Am ell).natAbs (M0Dual mq C kg Am)

/-- **`dXi_dvd_M0Dual`.**  `LEAN_PROVED`. -/
theorem dXi_dvd_M0Dual (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) :
    dXi mq C kg Am ell ∣ M0Dual mq C kg Am := Nat.gcd_dvd_right _ _

/-- **`dXi_dvd_Xi0`.**  `LEAN_PROVED`. -/
theorem dXi_dvd_Xi0 (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) :
    dXi mq C kg Am ell ∣ (Xi0 mq C kg Am ell).natAbs := Nat.gcd_dvd_left _ _

/-- **`dXi_pos`.**  `LEAN_PROVED`. -/
theorem dXi_pos {mq : ℕ} (h : 0 < mq) (C kg Am : ℤ) (ell : ℤ) : 0 < dXi mq C kg Am ell :=
  Nat.gcd_pos_of_pos_right _ (M0Dual_pos h C kg Am)

/-- The twice-reduced dual modulus `M' = M₀^dual / d_Ξ(ℓ)`. -/
def MPrime (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) : ℕ :=
  M0Dual mq C kg Am / dXi mq C kg Am ell

/-- The twice-reduced coordinate `Ξ'(ℓ) = Ξ₀(ℓ) / d_Ξ(ℓ)`. -/
def XiPrime (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) : ℤ :=
  Xi0 mq C kg Am ell / (dXi mq C kg Am ell : ℤ)

/-- **`MPrime_mul_dXi`.**  `LEAN_PROVED`.  Exact factorisation of the reduced modulus. -/
theorem MPrime_mul_dXi (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) :
    MPrime mq C kg Am ell * dXi mq C kg Am ell = M0Dual mq C kg Am :=
  Nat.div_mul_cancel (dXi_dvd_M0Dual mq C kg Am ell)

/-- **`XiPrime_mul_dXi`.**  `LEAN_PROVED`.  Exact factorisation of the reduced coordinate. -/
theorem XiPrime_mul_dXi (mq : ℕ) (C kg Am : ℤ) (ell : ℤ) :
    XiPrime mq C kg Am ell * (dXi mq C kg Am ell : ℤ) = Xi0 mq C kg Am ell := by
  refine Int.ediv_mul_cancel ?_
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (dXi_dvd_Xi0 mq C kg Am ell))

/-- **`xiRed_coprime`.**  `LEAN_PROVED`.  On a fixed `d_Ξ` packet the twice-reduced coordinate is
coprime to the twice-reduced modulus: `gcd(Ξ'(ℓ), M') = 1`. -/
theorem xiRed_coprime {mq : ℕ} (h : 0 < mq) (C kg Am : ℤ) (ell : ℤ) :
    Nat.Coprime (XiPrime mq C kg Am ell).natAbs (MPrime mq C kg Am ell) := by
  have hdvd : dXi mq C kg Am ell ∣ (Xi0 mq C kg Am ell).natAbs := dXi_dvd_Xi0 mq C kg Am ell
  have hnat : (XiPrime mq C kg Am ell).natAbs
      = (Xi0 mq C kg Am ell).natAbs / dXi mq C kg Am ell := by
    unfold XiPrime
    rw [Int.natAbs_ediv_of_dvd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd))]
    simp
  rw [hnat, MPrime, dXi]
  exact Nat.coprime_div_gcd_div_gcd (dXi_pos h C kg Am ell)

/-! ## §4  Variable-gcd residue uniqueness (unconditional) -/

/-- **`xi_divisor_affine_residue_unique`.**  `LEAN_PROVED`.  Unconditional finite arithmetic: for
**any** modulus `d` for which the reduced affine slope `s₀` is invertible (witness supplied), the
condition `d ∣ Ξ₀(ℓ)` places `ℓ` in a single residue class modulo `d`.

This is a uniqueness statement only.  It is **not** a tail bound, and the weighted large-gcd
router is not derivable from it: see `XiGcdTailBound`. -/
theorem xi_divisor_affine_residue_unique {mq : ℕ} {C kg Am : ℤ} {d : ℤ} {w : ℤ}
    (hw : s0 mq C kg Am * w ≡ 1 [ZMOD d]) {ell ell' : ℤ}
    (h : d ∣ Xi0 mq C kg Am ell) (h' : d ∣ Xi0 mq C kg Am ell') :
    ell ≡ ell' [ZMOD d] := by
  have key : c0 mq C kg Am + (-(s0 mq C kg Am)) * ell
      ≡ c0 mq C kg Am + (-(s0 mq C kg Am)) * ell' [ZMOD d] := by
    have hd : d ∣ (c0 mq C kg Am + (-(s0 mq C kg Am)) * ell)
        - (c0 mq C kg Am + (-(s0 mq C kg Am)) * ell') := by
      have hrw : (c0 mq C kg Am + (-(s0 mq C kg Am)) * ell)
          - (c0 mq C kg Am + (-(s0 mq C kg Am)) * ell')
          = Xi0 mq C kg Am ell - Xi0 mq C kg Am ell' := by unfold Xi0; ring
      rw [hrw]
      exact dvd_sub h h'
    exact (Int.modEq_iff_dvd.mpr (by simpa using (dvd_neg.mpr hd)))
  have hwneg : (-(s0 mq C kg Am)) * (-w) ≡ 1 [ZMOD d] := by simpa using hw
  exact affine_residue_unique_of_unit_slope hwneg key

/-! ## §5  Constant vs variable gcd: a separation theorem -/

/-- **`constant_and_variable_xi_gcd_differ`.**  `LEAN_PROVED`.  The constant gcd `d_const` and
the variable gcd `d_Ξ(ℓ)` are genuinely different objects: an explicit instance in which
`d_const = 1` while `d_Ξ(0) = 3`.  Nothing in this bank conflates them. -/
theorem constant_and_variable_xi_gcd_differ :
    dConst 9 3 0 1 = 1 ∧ dXi 9 3 0 1 0 = 3 := by
  constructor <;> decide +kernel

/-! ## §6  The large-`Ξ`-gcd router: explicit interface -/

/-- Explicit interface for the source-weighted large-`Ξ`-gcd tail.  The research statement is a
*weighted relative-mass* bound; it is recorded here as a hypothesis over an explicit finite
weight vector, never derived from residue uniqueness. -/
def XiGcdTailBound (s : Finset ℤ) (weight : ℤ → ℝ) (mq : ℕ) (C kg Am : ℤ) (G0 : ℕ) (K : ℝ) :
    Prop :=
  ∑ ell ∈ s.filter (fun ell => G0 ≤ dXi mq C kg Am ell), weight ell
    ≤ K * ∑ ell ∈ s, weight ell

/-- **`xiGcdTailBound_not_automatic`.**  `LEAN_PROVED`.  The tail interface is a genuine
hypothesis: there are finite data for which it fails.  Hence residue uniqueness alone does not
give `DUALLEVEL-XIGCD-ROUTER45`. -/
theorem xiGcdTailBound_not_automatic :
    ∃ (s : Finset ℤ) (weight : ℤ → ℝ) (mq : ℕ) (C kg Am : ℤ) (G0 : ℕ) (K : ℝ),
      ¬ XiGcdTailBound s weight mq C kg Am G0 K := by
  refine ⟨{0}, fun _ => 1, 1, 0, 0, 0, 0, 0, ?_⟩
  intro h
  simp only [XiGcdTailBound] at h
  norm_num at h

/-- **`xiGcdTailBound_satisfiable`.**  `LEAN_PROVED`.  The interface is also not contradictory:
it holds for the empty source.  So theorems carrying it are neither vacuous nor automatic. -/
theorem xiGcdTailBound_satisfiable :
    XiGcdTailBound (∅ : Finset ℤ) (fun _ => 1) 1 0 0 0 0 0 := by
  simp [XiGcdTailBound]

end TransverseDualXi
end Erdos287
