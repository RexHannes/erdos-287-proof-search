import Mathlib
import RequestProject.CurrentProgramme.PrimitiveDMultiplicity

/-!
# Fixed-`D` shared-`g₀` solution parametrisation — Erdős #287, SHARED-g₀ REPAIR Δ, §2

**Exact integer algebra and exact finite residue counting.**

With `g₁ = g₀r₁`, `g₂ = g₀r₂`, `gcd(r₁,r₂) = 1` and `D = t₁r₂ - t₂r₁`, the solutions of the
fixed-`D` equation form the line

```
t₁ = t₁⁰ + r₁ u,      t₂ = t₂⁰ + r₂ u,
```

and the physically relevant parameter is `u` **modulo `g₀`**.  Proved here:

* `sharedG0_u_param_iff` — the exact equivalence: `(t₁,t₂)` solves the fixed-`D` equation iff
  it is of the above form (forward direction via the banked
  `Erdos287.PrimitiveD.dLine_solution_form`);
* `sharedG0_u_period` — the residue system: shifting `u` by `g₀` changes `t₁` by `g₁` and
  `t₂` by `g₂`, so the pair `(t₁ mod g₁, t₂ mod g₂)` depends only on `u mod g₀`;
* `primitive_not_dvd_t1` / `_t2` — for `p ∣ g₀`, primitivity forces `p ∤ t₁` and `p ∤ t₂`,
  i.e. the two primitive exclusions on `u`;
* `excludedU_mem_iff` — the excluded `u`'s modulo a prime `p ∣ g₀` are exactly two explicit
  residues;
* `excludedU_eq_iff_dvd_D` — **the two forbidden residues coincide iff `p ∣ D`**;
* `nuP` and `card_excludedU` — hence the exact local count `ν_p(D) = 1` if `p ∣ D` and `2`
  otherwise.

Research status: `DET1-SHAREDG0-PRIMITIVE-U-PARAM45 : FORMALLY PROVED.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace Erdos287
namespace SharedG0Param

open Erdos287.PrimitiveD

/-! ## §2.1  The solution line and its residue system -/

/-- **Exact fixed-`D` parametrisation.**  `LEAN_PROVED`.

Given one solution `(t₁⁰,t₂⁰)` of `r₂t₁ - r₁t₂ = D` with `gcd(r₁,r₂) = 1`, `r₁ ≠ 0`, the
solutions are exactly the points of the line `t₁ = t₁⁰ + r₁u`, `t₂ = t₂⁰ + r₂u`. -/
theorem sharedG0_u_param_iff {r1 r2 t1 t2 t10 t20 D : ℤ} (hcop : IsCoprime r1 r2)
    (hr1 : r1 ≠ 0) (h0 : r2 * t10 - r1 * t20 = D) :
    r2 * t1 - r1 * t2 = D ↔ ∃ u : ℤ, t1 = t10 + r1 * u ∧ t2 = t20 + r2 * u := by
  constructor
  · intro h
    exact dLine_solution_form hcop hr1 h h0
  · rintro ⟨u, rfl, rfl⟩
    rw [← h0]; ring

/-- **The residue system.**  `LEAN_PROVED`.  Shifting the parameter by `g₀` shifts `t₁` by
`g₁ = g₀r₁` and `t₂` by `g₂ = g₀r₂`; hence the physical data depends only on `u mod g₀`. -/
theorem sharedG0_u_period {g0 r1 r2 t10 t20 u k : ℤ} :
    (t10 + r1 * (u + g0 * k)) - (t10 + r1 * u) = (g0 * r1) * k ∧
      (t20 + r2 * (u + g0 * k)) - (t20 + r2 * u) = (g0 * r2) * k := by
  constructor <;> ring

/-! ## §2.2  The primitive exclusions -/

/-- Primitivity `gcd(t₁, g₀r₁) = 1` forces `p ∤ t₁` for every `p ∣ g₀`: the first primitive
exclusion on `u`. -/
theorem primitive_not_dvd_t1 {g0 r1 p : ℕ} {t1 : ℤ} (hp : 1 < p) (hpg : p ∣ g0)
    (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1) : ¬ (p : ℤ) ∣ t1 := by
  intro hdvd
  have hpg1 : (p : ℤ) ∣ (g0 : ℤ) * r1 :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hpg) _
  have hd : p ∣ Int.gcd t1 ((g0 : ℤ) * r1) := Int.dvd_gcd hdvd hpg1
  rw [h1] at hd
  have := Nat.dvd_one.mp hd
  omega

/-- Primitivity `gcd(t₂, g₀r₂) = 1` forces `p ∤ t₂` for every `p ∣ g₀`: the second primitive
exclusion on `u`. -/
theorem primitive_not_dvd_t2 {g0 r2 p : ℕ} {t2 : ℤ} (hp : 1 < p) (hpg : p ∣ g0)
    (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) : ¬ (p : ℤ) ∣ t2 := by
  intro hdvd
  have hpg2 : (p : ℤ) ∣ (g0 : ℤ) * r2 :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hpg) _
  have hd : p ∣ Int.gcd t2 ((g0 : ℤ) * r2) := Int.dvd_gcd hdvd hpg2
  rw [h2] at hd
  have := Nat.dvd_one.mp hd
  omega

/-! ## §2.3  The two forbidden residues modulo `p` -/

variable {p : ℕ}

/-- The set of `u` modulo `p` excluded by the two primitive conditions. -/
def excludedU (p : ℕ) (t10 t20 r1 r2 : ℤ) : Finset (ZMod p) :=
  {-(t10 : ZMod p) * ((r1 : ZMod p))⁻¹, -(t20 : ZMod p) * ((r2 : ZMod p))⁻¹}

/-- **Membership.**  `LEAN_PROVED`.  For `p` prime with `p ∤ r₁r₂`, the excluded residues are
exactly the `u` violating one of the two primitive conditions. -/
theorem excludedU_mem_iff (hp : p.Prime) {t10 t20 r1 r2 : ℤ}
    (hr1 : ¬ (p : ℤ) ∣ r1) (hr2 : ¬ (p : ℤ) ∣ r2) (u : ZMod p) :
    u ∈ excludedU p t10 t20 r1 r2 ↔
      ((t10 : ZMod p) + (r1 : ZMod p) * u = 0 ∨ (t20 : ZMod p) + (r2 : ZMod p) * u = 0) := by
  haveI := Fact.mk hp
  have hr1' : (r1 : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hr1
  have hr2' : (r2 : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hr2
  rw [excludedU, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · left
      field_simp
      ring
    · right
      field_simp
      ring
  · rintro (h | h)
    · left
      field_simp
      linear_combination h
    · right
      field_simp
      linear_combination h

/-- **The coincidence criterion.**  `LEAN_PROVED`.

The two forbidden residues coincide **iff** `p ∣ D`, where `D = t₁⁰r₂ - t₂⁰r₁`. -/
theorem excludedU_eq_iff_dvd_D (hp : p.Prime) {t10 t20 r1 r2 : ℤ}
    (hr1 : ¬ (p : ℤ) ∣ r1) (hr2 : ¬ (p : ℤ) ∣ r2) :
    (-(t10 : ZMod p) * ((r1 : ZMod p))⁻¹ = -(t20 : ZMod p) * ((r2 : ZMod p))⁻¹)
      ↔ (p : ℤ) ∣ (t10 * r2 - t20 * r1) := by
  haveI := Fact.mk hp
  have hr1' : (r1 : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hr1
  have hr2' : (r2 : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hr2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor
  · intro h
    have h2 : (t10 : ZMod p) * (r2 : ZMod p) = (t20 : ZMod p) * (r1 : ZMod p) := by
      field_simp at h
      linear_combination -h
    rw [h2]; ring
  · intro h
    have h2 : (t10 : ZMod p) * (r2 : ZMod p) = (t20 : ZMod p) * (r1 : ZMod p) := by
      linear_combination h
    field_simp
    linear_combination -h2

/-- `ν_p(D) = 1` if `p ∣ D`, and `2` otherwise. -/
def nuP (p : ℕ) (D : ℤ) : ℕ := if (p : ℤ) ∣ D then 1 else 2

/-- **`DET1-SHAREDG0-PRIMITIVE-U-PARAM45`, local count.**  `LEAN_PROVED`.

The number of excluded residues `u mod p` is exactly `ν_p(D)`. -/
theorem card_excludedU (hp : p.Prime) {t10 t20 r1 r2 : ℤ}
    (hr1 : ¬ (p : ℤ) ∣ r1) (hr2 : ¬ (p : ℤ) ∣ r2) :
    (excludedU p t10 t20 r1 r2).card = nuP p (t10 * r2 - t20 * r1) := by
  haveI := Fact.mk hp
  by_cases h : (p : ℤ) ∣ (t10 * r2 - t20 * r1)
  · have heq := (excludedU_eq_iff_dvd_D hp hr1 hr2).2 h
    rw [excludedU, heq, nuP, if_pos h]
    simp
  · have hne : ¬ (-(t10 : ZMod p) * ((r1 : ZMod p))⁻¹ = -(t20 : ZMod p) * ((r2 : ZMod p))⁻¹) :=
      fun hcon => h ((excludedU_eq_iff_dvd_D hp hr1 hr2).1 hcon)
    rw [excludedU, nuP, if_neg h, Finset.card_pair hne]

end SharedG0Param
end Erdos287
