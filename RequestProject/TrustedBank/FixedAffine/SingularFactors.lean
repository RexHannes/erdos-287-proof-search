import Mathlib
import RequestProject.TrustedBank.FixedAffine.LocalRoots
import RequestProject.TrustedBank.Erdos287.BoundedCofactor

/-!
# Trusted bank — Bank F: local singular factors (no infinite product)

For a bounded-cofactor Bézout pair `P n = e n + u`, `Q n = d n + v` (`e v - d u = 1`)
and a prime `ℓ`, let `ν(ℓ)` be the number of residues `n mod ℓ` killed by `P` or `Q`.
We prove exactly:

* `ν(ℓ) = 1` when `ℓ ∣ d e`;
* `ν(ℓ) = 2` when `ℓ ∤ d e`;

and we compute the induced finite *rational* correction factor for odd `ℓ ∣ d e`,
namely `(ℓ - 1) / (ℓ - 2)`.

The infinite Euler product is deliberately **not** formalized here: only the local
factors are banked.
-/

open scoped BigOperators

namespace TrustedBank
namespace SingularFactors

open BoundedCofactor LocalRoots

variable (B : Bez) (l : ℕ) [Fact (Nat.Prime l)]

/-- The set of residues mod `ℓ` killed by `P` or by `Q`. -/
def rootSet : Finset (ZMod l) :=
  Finset.univ.filter
    (fun n => (B.e : ZMod l) * n + (B.u : ZMod l) = 0 ∨ (B.d : ZMod l) * n + (B.v : ZMod l) = 0)

/-- The local root count `ν(ℓ)`. -/
def nu : ℕ := (rootSet B l).card

theorem rootSet_eq_union :
    rootSet B l = linRoots (B.e : ZMod l) (B.u : ZMod l) ∪ linRoots (B.d : ZMod l) (B.v : ZMod l) := by
  unfold rootSet linRoots
  rw [← Finset.filter_or]

/-- The Bézout relation, read in `ZMod ℓ`. -/
theorem bez_zmod :
    (B.e : ZMod l) * (B.v : ZMod l) - (B.d : ZMod l) * (B.u : ZMod l) = 1 := by
  have := congrArg (fun z : ℤ => (z : ZMod l)) B.bez
  push_cast at this
  simpa using this

/-- A prime dividing one member of a coprime pair cannot divide the other. -/
theorem not_dvd_of_isCoprime {a b : ℤ} (h : IsCoprime a b) (hla : (l : ℤ) ∣ a) :
    ¬ (l : ℤ) ∣ b := by
  intro hlb
  have : IsUnit (l : ℤ) := h.isUnit_of_dvd' hla hlb
  exact (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime l)).not_unit this

/-- **Bank F.1 — `ν(ℓ) = 2` for `ℓ ∤ d e`.** -/
theorem nu_eq_two (h : ¬ ((l : ℤ) ∣ B.d * B.e)) : nu B l = 2 := by
  have hd : ((B.d : ZMod l)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hc => h (hc.mul_right _)
  have he : ((B.e : ZMod l)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hc => h (hc.mul_left _)
  have hne : (-(B.u : ZMod l) / (B.e : ZMod l)) ≠ (-(B.v : ZMod l) / (B.d : ZMod l)) := by
    intro hEq
    set x : ZMod l := -(B.u : ZMod l) / (B.e : ZMod l) with hx
    have hP : (B.e : ZMod l) * x + (B.u : ZMod l) = 0 := by
      rw [hx]; field_simp; ring
    have hQ : (B.d : ZMod l) * x + (B.v : ZMod l) = 0 := by
      rw [hEq]; field_simp; ring
    have h1 : (1 : ZMod l) = 0 := by
      have := bez_zmod B l
      calc (1 : ZMod l)
          = (B.e : ZMod l) * (B.v : ZMod l) - (B.d : ZMod l) * (B.u : ZMod l) := this.symm
        _ = (B.e : ZMod l) * ((B.d : ZMod l) * x + (B.v : ZMod l))
              - (B.d : ZMod l) * ((B.e : ZMod l) * x + (B.u : ZMod l)) := by ring
        _ = 0 := by rw [hP, hQ]; ring
    exact one_ne_zero h1
  unfold nu
  rw [rootSet_eq_union, linRoots_of_ne_zero he, linRoots_of_ne_zero hd,
    Finset.singleton_union, Finset.card_insert_of_notMem (by simpa using hne),
    Finset.card_singleton]

/-- **Bank F.2 — `ν(ℓ) = 1` for `ℓ ∣ d e`.** -/
theorem nu_eq_one (h : (l : ℤ) ∣ B.d * B.e) : nu B l = 1 := by
  have hprime : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime l)
  unfold nu
  rcases hprime.dvd_mul.1 h with hD | hE
  · -- `ℓ ∣ d`: `Q` has no root, `P` has exactly one
    have hv : ¬ (l : ℤ) ∣ B.v := not_dvd_of_isCoprime l B.isCoprime_d_v hD
    have he : ¬ (l : ℤ) ∣ B.e := not_dvd_of_isCoprime l B.isCoprime_d_e hD
    have hd0 : ((B.d : ZMod l)) = 0 := by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hD
    have hv0 : ((B.v : ZMod l)) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hv
    have he0 : ((B.e : ZMod l)) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact he
    rw [rootSet_eq_union, linRoots_of_eq_zero hd0 hv0, linRoots_of_ne_zero he0,
      Finset.union_empty, Finset.card_singleton]
  · -- `ℓ ∣ e`: `P` has no root, `Q` has exactly one
    have hu : ¬ (l : ℤ) ∣ B.u := not_dvd_of_isCoprime l B.isCoprime_e_u hE
    have hd : ¬ (l : ℤ) ∣ B.d := fun hc => not_dvd_of_isCoprime l B.isCoprime_d_e hc hE
    have he0 : ((B.e : ZMod l)) = 0 := by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hE
    have hu0 : ((B.u : ZMod l)) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hu
    have hd0 : ((B.d : ZMod l)) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd
    rw [rootSet_eq_union, linRoots_of_eq_zero he0 hu0, linRoots_of_ne_zero hd0,
      Finset.empty_union, Finset.card_singleton]

/-! ## The finite local correction factor -/

/-- The local density factor `(1 - ν/ℓ) (1 - 1/ℓ)⁻²` attached to a root count `ν`. -/
def localFactor (nu l : ℚ) : ℚ := (1 - nu / l) / (1 - 1 / l) ^ 2

/-- **Bank F.3 — the finite rational correction factor.**  For an odd prime `ℓ`
(`ℓ ≥ 3`), passing from the generic root count `2` to the bounded-cofactor root count
`1` multiplies the local factor by exactly `(ℓ - 1)/(ℓ - 2)`. -/
theorem localFactor_ratio {l : ℚ} (hl : 3 ≤ l) :
    localFactor 1 l = ((l - 1) / (l - 2)) * localFactor 2 l := by
  have h0 : l ≠ 0 := by intro h; rw [h] at hl; norm_num at hl
  have h1 : l - 1 ≠ 0 := by intro h; nlinarith
  have h2 : l - 2 ≠ 0 := by intro h; nlinarith
  unfold localFactor
  field_simp

/-- **Bank F.4 — the correction factor for an odd prime dividing `d e`.**  Combining
`nu_eq_one` with `localFactor_ratio`. -/
theorem localFactor_of_dvd (hl3 : 3 ≤ l) (h : (l : ℤ) ∣ B.d * B.e) :
    localFactor (nu B l : ℚ) (l : ℚ)
      = (((l : ℚ) - 1) / ((l : ℚ) - 2)) * localFactor 2 (l : ℚ) := by
  rw [nu_eq_one B l h]
  exact_mod_cast localFactor_ratio (l := (l : ℚ)) (by exact_mod_cast hl3)

end SingularFactors
end TrustedBank
