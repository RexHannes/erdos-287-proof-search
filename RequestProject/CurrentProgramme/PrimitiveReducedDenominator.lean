import Mathlib
import RequestProject.CurrentProgramme.PrimitiveFareyNearCollision

/-!
# Reduced denominator of the shared-`g₀` frequency — Erdős #287, SHARED-g₀ REPAIR Δ, §6

**Exact integer / rational algebra only.**  Nothing analytic, nothing asymptotic.

Setting (the shared-`g₀` parametrisation of the repository):

```
g₁ = g₀ r₁,   g₂ = g₀ r₂,   gcd(r₁,r₂) = 1,
Λ  = lcm(g₁,g₂) = g₀ r₁ r₂,
D  = t₁ r₂ - t₂ r₁,
```

with the **primitivity** hypotheses `gcd(t₁,g₁) = 1`, `gcd(t₂,g₂) = 1`.

Proved here:

* `lcm_sharedG0_eq` — `lcm(g₀r₁, g₀r₂) = g₀r₁r₂` (re-exported from the banked
  `Erdos287.PrimitiveFarey.lcm_of_coprime_cofactors`; not re-proved);
* `gcd_D_lambda_coprime_left` / `_right` — `gcd(D,Λ)` is coprime to `r₁` and to `r₂`;
* `gcd_D_lambda_dvd_g0` — **`DET1-PRIMITIVE-REDUCED-DENOMINATOR45`, core**: `gcd(D,Λ) ∣ g₀`.
  The proof is prime-by-prime and makes **no squarefreeness assumption**: it is
  valuation-safe and holds for arbitrary `g₀, r₁, r₂ ≥ 1` and arbitrary primitive `t₁,t₂`;
* `reducedDenominator_eq` — `den(D/Λ) = Λ / gcd(D,Λ)`;
* `reducedDenominator_ge` — hence `den(D/Λ) ≥ r₁r₂ = g₁g₂/g₀²`.

Research status: `DET1-PRIMITIVE-REDUCED-DENOMINATOR45 : FORMALLY PROVED.`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace ReducedDenominator

open Erdos287.PrimitiveFarey

/-! ## §6.1  The modulus -/

/-- `lcm(g₀r₁, g₀r₂) = g₀r₁r₂` for coprime cofactors — the banked statement of §E,
re-exported here for use in the shared-`g₀` denominator algebra. -/
theorem lcm_sharedG0_eq {g0 r1 r2 : ℕ} (hg0 : 0 < g0) (hcop : Nat.Coprime r1 r2) :
    Nat.lcm (g0 * r1) (g0 * r2) = g0 * r1 * r2 :=
  lcm_of_coprime_cofactors hg0 hcop

/-! ## §6.2  `gcd(D,Λ) ∣ g₀`, prime by prime -/

/-- `gcd(D,Λ)` is coprime to `r₁`.

Prime-by-prime: a prime `p ∣ r₁` dividing `D = t₁r₂ - t₂r₁` would divide `t₁r₂`; primitivity
`gcd(t₁, g₀r₁) = 1` excludes `p ∣ t₁`, and `gcd(r₁,r₂) = 1` excludes `p ∣ r₂`. -/
theorem gcd_D_lambda_coprime_left {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hcop : Nat.Coprime r1 r2)
    (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1) (Λ : ℕ) :
    Nat.Coprime (Int.gcd (t1 * r2 - t2 * r1) (Λ : ℤ)) r1 := by
  by_contra hcon
  obtain ⟨p, hp, hpd, hpr1⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcon
  have hpD : (p : ℤ) ∣ (t1 * (r2 : ℤ) - t2 * r1) :=
    dvd_trans (Int.natCast_dvd_natCast.2 hpd) (Int.gcd_dvd_left _ _)
  have hpr1z : (p : ℤ) ∣ (r1 : ℤ) := Int.natCast_dvd_natCast.2 hpr1
  have hpt : (p : ℤ) ∣ t1 * (r2 : ℤ) := by
    have h2 : (p : ℤ) ∣ t2 * (r1 : ℤ) := Dvd.dvd.mul_left hpr1z t2
    have := dvd_add hpD h2
    simpa using this
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hprime.dvd_mul.1 hpt with h | h
  · have hdvd : (p : ℤ) ∣ (g0 : ℤ) * r1 := Dvd.dvd.mul_left hpr1z _
    have hgd : p ∣ Int.gcd t1 ((g0 : ℤ) * r1) := Int.dvd_gcd h hdvd
    rw [h1] at hgd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgd)
  · have hpr2 : p ∣ r2 := Int.natCast_dvd_natCast.1 h
    have hgd : p ∣ Nat.gcd r1 r2 := Nat.dvd_gcd hpr1 hpr2
    rw [hcop] at hgd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgd)

/-- `gcd(D,Λ)` is coprime to `r₂`, by the mirror argument. -/
theorem gcd_D_lambda_coprime_right {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hcop : Nat.Coprime r1 r2)
    (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) (Λ : ℕ) :
    Nat.Coprime (Int.gcd (t1 * r2 - t2 * r1) (Λ : ℤ)) r2 := by
  by_contra hcon
  obtain ⟨p, hp, hpd, hpr2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcon
  have hpD : (p : ℤ) ∣ (t1 * (r2 : ℤ) - t2 * r1) :=
    dvd_trans (Int.natCast_dvd_natCast.2 hpd) (Int.gcd_dvd_left _ _)
  have hpr2z : (p : ℤ) ∣ (r2 : ℤ) := Int.natCast_dvd_natCast.2 hpr2
  have hpt : (p : ℤ) ∣ t2 * (r1 : ℤ) := by
    have h1 : (p : ℤ) ∣ t1 * (r2 : ℤ) := Dvd.dvd.mul_left hpr2z t1
    have := dvd_sub h1 hpD
    simpa using this
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hprime.dvd_mul.1 hpt with h | h
  · have hdvd : (p : ℤ) ∣ (g0 : ℤ) * r2 := Dvd.dvd.mul_left hpr2z _
    have hgd : p ∣ Int.gcd t2 ((g0 : ℤ) * r2) := Int.dvd_gcd h hdvd
    rw [h2] at hgd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgd)
  · have hpr1 : p ∣ r1 := Int.natCast_dvd_natCast.1 h
    have hgd : p ∣ Nat.gcd r1 r2 := Nat.dvd_gcd hpr1 hpr2
    rw [hcop] at hgd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hgd)

/-- **`DET1-PRIMITIVE-REDUCED-DENOMINATOR45`, core.**  `LEAN_PROVED`.

With `Λ = g₀r₁r₂ = lcm(g₁,g₂)` and `D = t₁r₂ - t₂r₁` under the primitivity hypotheses
`gcd(t₁,g₀r₁) = gcd(t₂,g₀r₂) = 1` and `gcd(r₁,r₂) = 1`:

```
gcd(D, Λ) ∣ g₀.
```

No squarefreeness is assumed anywhere: the argument is prime-by-prime and therefore safe for
arbitrary `p`-adic valuations of `g₀, r₁, r₂`. -/
theorem gcd_D_lambda_dvd_g0 {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hcop : Nat.Coprime r1 r2)
    (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1) (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) :
    Int.gcd (t1 * r2 - t2 * r1) ((g0 * r1 * r2 : ℕ) : ℤ) ∣ g0 := by
  set d : ℕ := Int.gcd (t1 * (r2 : ℤ) - t2 * r1) ((g0 * r1 * r2 : ℕ) : ℤ) with hd
  have hdvd : d ∣ g0 * r1 * r2 := by
    have : (d : ℤ) ∣ ((g0 * r1 * r2 : ℕ) : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hc1 : Nat.Coprime d r1 := gcd_D_lambda_coprime_left hcop h1 (g0 * r1 * r2)
  have hc2 : Nat.Coprime d r2 := gcd_D_lambda_coprime_right hcop h2 (g0 * r1 * r2)
  have hstep : d ∣ g0 * r1 := hc2.dvd_of_dvd_mul_right hdvd
  exact hc1.dvd_of_dvd_mul_right hstep

/-! ## §6.3  The reduced denominator -/

/-- **Exact reduced denominator.**  `LEAN_PROVED`.

For `Λ > 0` the rational `D/Λ` has denominator exactly `Λ / gcd(D,Λ)`. -/
theorem reducedDenominator_eq (D : ℤ) {Λ : ℕ} (hΛ : 0 < Λ) :
    ((D : ℚ) / (Λ : ℚ)).den = Λ / Int.gcd D (Λ : ℤ) := by
  set g : ℕ := Int.gcd D (Λ : ℤ) with hg
  have hΛz : (0 : ℤ) < (Λ : ℤ) := by exact_mod_cast hΛ
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right D (ne_of_gt hΛz)
  have hgz : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
  have hgD : (g : ℤ) ∣ D := Int.gcd_dvd_left _ _
  have hgΛ : (g : ℤ) ∣ (Λ : ℤ) := Int.gcd_dvd_right _ _
  have hcop : Int.gcd (D / (g : ℤ)) ((Λ : ℤ) / (g : ℤ)) = 1 :=
    Int.gcd_div_gcd_div_gcd hgpos
  have hbpos : (0 : ℤ) < (Λ : ℤ) / (g : ℤ) := Int.ediv_pos_of_pos_of_dvd hΛz (le_of_lt hgz) hgΛ
  have hcast : (D : ℚ) / (Λ : ℚ) = ((D / (g : ℤ) : ℤ) : ℚ) / (((Λ : ℤ) / (g : ℤ) : ℤ) : ℚ) := by
    obtain ⟨a, ha⟩ := hgD
    obtain ⟨b, hb⟩ := hgΛ
    have hgne : ((g : ℤ) : ℚ) ≠ 0 := by
      have : (g : ℤ) ≠ 0 := ne_of_gt hgz
      exact_mod_cast this
    have hDg : D / (g : ℤ) = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hgz)
    have hLg : (Λ : ℤ) / (g : ℤ) = b := by rw [hb]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hgz)
    have haQ : (D : ℚ) = ((g : ℤ) : ℚ) * (a : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) ha
    have hbQ : ((Λ : ℕ) : ℚ) = ((g : ℤ) : ℚ) * (b : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hb
    rw [hDg, hLg, haQ, hbQ, mul_div_mul_left _ _ hgne]
  have hden := Rat.den_div_eq_of_coprime (a := D / (g : ℤ)) (b := (Λ : ℤ) / (g : ℤ)) hbpos
    (by simpa [Int.gcd] using hcop)
  have hnat : (((D : ℚ) / (Λ : ℚ)).den : ℤ) = (Λ : ℤ) / (g : ℤ) := by
    rw [hcast]; exact hden
  have hcast2 : ((Λ : ℤ) / (g : ℤ)) = ((Λ / g : ℕ) : ℤ) := by
    exact Int.ofNat_ediv_ofNat
  exact_mod_cast hnat.trans hcast2

/-- **`DET1-PRIMITIVE-REDUCED-DENOMINATOR45`.**  `LEAN_PROVED`.

Under the primitive shared-`g₀` hypotheses, the reduced denominator of `D/Λ` is at least
`r₁r₂ = g₁g₂/g₀²`. -/
theorem reducedDenominator_ge {g0 r1 r2 : ℕ} {t1 t2 : ℤ} (hg0 : 0 < g0) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hcop : Nat.Coprime r1 r2) (h1 : Int.gcd t1 ((g0 : ℤ) * r1) = 1)
    (h2 : Int.gcd t2 ((g0 : ℤ) * r2) = 1) :
    r1 * r2 ≤ (((t1 * r2 - t2 * r1 : ℤ) : ℚ) / ((g0 * r1 * r2 : ℕ) : ℚ)).den := by
  have hΛ : 0 < g0 * r1 * r2 := by positivity
  have hden := reducedDenominator_eq (t1 * (r2 : ℤ) - t2 * r1) hΛ
  have hdvd := gcd_D_lambda_dvd_g0 hcop h1 h2
  set d : ℕ := Int.gcd (t1 * (r2 : ℤ) - t2 * r1) ((g0 * r1 * r2 : ℕ) : ℤ) with hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hg0
  have hdle : d ≤ g0 := Nat.le_of_dvd hg0 hdvd
  have hmono : (g0 * r1 * r2) / g0 ≤ (g0 * r1 * r2) / d := Nat.div_le_div_left hdle hdpos
  have hexact : (g0 * r1 * r2) / g0 = r1 * r2 := by
    rw [mul_assoc]
    exact Nat.mul_div_cancel_left _ hg0
  rw [hden]
  omega

end ReducedDenominator
end Erdos287
