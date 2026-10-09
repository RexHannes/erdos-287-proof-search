import RequestProject.Erdos287.PostV87V90R.ContactCycle

/-!
# Erdős #287 — post-V87 → V90R: the affine adjacency compiler algebra

**ERDŐS #287 REMAINS OPEN.  This file is exact integer algebra.**

For positive integer slopes `aᵢ < aⱼ` with `d = aⱼ - aᵢ = gcd(aᵢ, aⱼ)` put

* `n⁻ᵢⱼ(t) = (aᵢ/d)(aⱼ t + 1)`, `n⁺ᵢⱼ(t) = (aⱼ/d)(aᵢ t + 1)`.

Proved unconditionally:

* `gcd_eq_sub_iff` — `gcd(aᵢ,aⱼ) = aⱼ - aᵢ ↔ (aⱼ - aᵢ) ∣ aᵢ`;
* `affine_adjacency` — **`n⁺ᵢⱼ(t) = n⁻ᵢⱼ(t) + 1`** for every `t`;
* the integrality / divisibility side conditions `nMinus_mul_d`, `nPlus_mul_d`,
  `form_dvd_nMinus`, `form_dvd_nPlus`, `nMinus_eq_cofactor_mul`, `nPlus_eq_cofactor_mul`.

`AffineContactCompiler r m K` is the finite compiler *data*: `K` affine forms `a t + 1` per
macroblock `j ∈ ZMod r`, with positivity, distinctness across graph edges and the gcd
condition on every edge of `ContactCycle r m`, plus an explicit scale-ratio bound.  No inhabitant
is constructed in this subtree for the W3 / `E287_11_4` parameters: the CRT prescription for
the slopes is not in the repository.  (The structure is *data with proved fields*, not a
`Prop`-valued placeholder.)
-/

namespace Erdos287.PostV87V90R

/-- `n⁻ᵢⱼ(t) = (aᵢ/d)(aⱼ t + 1)` with `d = aⱼ - aᵢ`. -/
def nMinus (ai aj t : ℕ) : ℕ := ai / (aj - ai) * (aj * t + 1)

/-- `n⁺ᵢⱼ(t) = (aⱼ/d)(aᵢ t + 1)` with `d = aⱼ - aᵢ`. -/
def nPlus (ai aj t : ℕ) : ℕ := aj / (aj - ai) * (ai * t + 1)

theorem sub_dvd_right {ai aj : ℕ} (hlt : ai < aj) (hd : (aj - ai) ∣ ai) : (aj - ai) ∣ aj := by
  have h := Nat.dvd_add hd (dvd_refl (aj - ai))
  rwa [Nat.add_sub_cancel' hlt.le] at h

/-- The gcd condition `d = gcd(aᵢ,aⱼ)` is equivalent to `d ∣ aᵢ` (for `aᵢ < aⱼ`). -/
theorem gcd_eq_sub_iff {ai aj : ℕ} (hlt : ai < aj) :
    Nat.gcd ai aj = aj - ai ↔ (aj - ai) ∣ ai := by
  constructor
  · intro h; rw [← h]; exact Nat.gcd_dvd_left _ _
  · intro hd
    exact Nat.dvd_antisymm (Nat.dvd_sub (Nat.gcd_dvd_right ai aj) (Nat.gcd_dvd_left ai aj))
      (Nat.dvd_gcd hd (sub_dvd_right hlt hd))

/-- **Affine adjacency identity.**  If `aᵢ < aⱼ` and `(aⱼ - aᵢ) ∣ aᵢ` (equivalently
`aⱼ - aᵢ = gcd(aᵢ,aⱼ)`), then `n⁺ᵢⱼ(t) = n⁻ᵢⱼ(t) + 1` for every `t`. -/
theorem affine_adjacency {ai aj : ℕ} (hlt : ai < aj) (hd : (aj - ai) ∣ ai) (t : ℕ) :
    nPlus ai aj t = nMinus ai aj t + 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, aj = ai + d := ⟨aj - ai, by omega⟩
  have hdpos : 0 < d := by omega
  simp only [Nat.add_sub_cancel_left] at hd
  obtain ⟨u, rfl⟩ := hd
  unfold nPlus nMinus
  rw [Nat.add_sub_cancel_left]
  have e1 : d * u / d = u := Nat.mul_div_cancel_left _ hdpos
  have e2 : (d * u + d) / d = u + 1 := by
    rw [show d * u + d = d * (u + 1) by ring]; exact Nat.mul_div_cancel_left _ hdpos
  rw [e1, e2]
  ring

/-- Integrality: `n⁻ · d = aᵢ (aⱼ t + 1)`. -/
theorem nMinus_mul_d {ai aj : ℕ} (hd : (aj - ai) ∣ ai) (t : ℕ) :
    nMinus ai aj t * (aj - ai) = ai * (aj * t + 1) := by
  unfold nMinus
  rw [mul_comm (ai / (aj - ai)), mul_assoc, Nat.div_mul_cancel hd, mul_comm]

/-- Integrality: `n⁺ · d = aⱼ (aᵢ t + 1)`. -/
theorem nPlus_mul_d {ai aj : ℕ} (hlt : ai < aj) (hd : (aj - ai) ∣ ai) (t : ℕ) :
    nPlus ai aj t * (aj - ai) = aj * (ai * t + 1) := by
  unfold nPlus
  rw [mul_comm (aj / (aj - ai)), mul_assoc, Nat.div_mul_cancel (sub_dvd_right hlt hd), mul_comm]

/-- The prime-form value `aⱼ t + 1` divides `n⁻`, with cofactor `aᵢ/d`. -/
theorem nMinus_eq_cofactor_mul (ai aj t : ℕ) :
    nMinus ai aj t = (aj * t + 1) * (ai / (aj - ai)) := by
  unfold nMinus; ring

/-- The prime-form value `aᵢ t + 1` divides `n⁺`, with cofactor `aⱼ/d`. -/
theorem nPlus_eq_cofactor_mul (ai aj t : ℕ) :
    nPlus ai aj t = (ai * t + 1) * (aj / (aj - ai)) := by
  unfold nPlus; ring

theorem form_dvd_nMinus (ai aj t : ℕ) : (aj * t + 1) ∣ nMinus ai aj t :=
  ⟨_, nMinus_eq_cofactor_mul ai aj t⟩

theorem form_dvd_nPlus (ai aj t : ℕ) : (ai * t + 1) ∣ nPlus ai aj t :=
  ⟨_, nPlus_eq_cofactor_mul ai aj t⟩

/-- Concrete sanity fixture: slopes `2 < 4` (`d = 2 = gcd`), `t = 1`: `n⁻ = 5`, `n⁺ = 6`. -/
example : nMinus 2 4 1 = 5 ∧ nPlus 2 4 1 = 6 := by decide

/-- **Finite affine contact compiler (data with proved fields).**  `K` affine forms
`slope j i · t + 1` per macroblock `j ∈ ZMod r`; every edge of `ContactCycle r m` joins forms with
distinct slopes satisfying the gcd condition; all slopes lie within the ratio `ratio`. -/
structure AffineContactCompiler (r m K : ℕ) [NeZero r] where
  /-- The slopes. -/
  slope : ZMod r → Fin K → ℕ
  slope_pos : ∀ j i, 0 < slope j i
  /-- Forms in adjacent macroblocks have distinct slopes. -/
  edge_ne : ∀ j k i i', (ContactCycle r m).Adj j k → slope j i ≠ slope k i'
  /-- **Graph-edge gcd condition:** on every edge, `aⱼ - aᵢ = gcd(aᵢ, aⱼ)`. -/
  edge_gcd : ∀ j k i i', (ContactCycle r m).Adj j k → slope j i < slope k i' →
    Nat.gcd (slope j i) (slope k i') = slope k i' - slope j i
  /-- Explicit scale-ratio bound between any two slopes. -/
  ratio : ℕ
  scale_ratio : ∀ j i j' i', slope j' i' ≤ ratio * slope j i

namespace AffineContactCompiler

variable {r m K : ℕ} [NeZero r] (C : AffineContactCompiler r m K)

/-- On every oriented compiler edge, the two compiled positions are adjacent integers. -/
theorem edge_adjacent {j k : ZMod r} {i i' : Fin K} (hadj : (ContactCycle r m).Adj j k)
    (hlt : C.slope j i < C.slope k i') (t : ℕ) :
    nPlus (C.slope j i) (C.slope k i') t = nMinus (C.slope j i) (C.slope k i') t + 1 :=
  affine_adjacency hlt ((gcd_eq_sub_iff hlt).1 (C.edge_gcd j k i i' hadj hlt)) t

end AffineContactCompiler

end Erdos287.PostV87V90R
