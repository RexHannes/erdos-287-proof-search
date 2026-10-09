import Mathlib

/-!
# Erdős #287 — Research Bank V18 §1: the colour-conductor reduction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Finite additive-character representation: `e_D(x) = exp(2πi x / D)` for integers `x` and
positive `D`.

For positive integers `D, c` put `g = gcd(D, c)`, `E = D/g`, `c₀ = c/g`.

Kernel-proved (LEAN BANK):
* `e_add`, `e_periodic`, `e_congr`, `e_scale` — the additive-character toolkit;
* `inverse_reduces` — an inverse of `z` modulo `D` is an inverse modulo every divisor `E ∣ D`,
  and any two inverses modulo `E` agree modulo `E`;
* **`colour_conductor_reduction`** — for every `h` and every unit `z` (with inverse `z̄` mod `D`
  and inverse `z̄'` mod `E`):  `e_D(h c z̄) = e_E(h c₀ z̄')`.  **No hypothesis that `c` is a unit
  mod `D`**;
* `colour_conductor_E_one` — the degenerate case `E = 1` (`D ∣ c`): the phase is identically `1`;
* `nonunit_fixture` — `D = 6`, `c = 4` (not a unit mod 6) reduces to `E = 3`, `c₀ = 2`.
-/

namespace Erdos287
namespace ResearchBankV18
namespace ColourConductor

open Complex

/-- The additive character `e_D(x) = exp(2πi x/D)`. -/
noncomputable def e (D : ℕ) (x : ℤ) : ℂ := Complex.exp (2 * Real.pi * I * x / D)

theorem e_add (D : ℕ) (x y : ℤ) : e D (x + y) = e D x * e D y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e_mul_self {D : ℕ} (hD : 0 < D) (k : ℤ) : e D (D * k) = 1 := by
  unfold e
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [show 2 * Real.pi * I * ((D * k : ℤ) : ℂ) / D = (k : ℂ) * (2 * Real.pi * I) by
    push_cast; field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- `e_D` is `D`-periodic. -/
theorem e_periodic {D : ℕ} (hD : 0 < D) (x k : ℤ) : e D (x + D * k) = e D x := by
  rw [e_add, e_mul_self hD, mul_one]

/-- `e_D` only depends on the residue mod `D`. -/
theorem e_congr {D : ℕ} (hD : 0 < D) {x y : ℤ} (h : x ≡ y [ZMOD D]) : e D x = e D y := by
  obtain ⟨k, hk⟩ := (Int.modEq_iff_dvd.1 h.symm)
  rw [show x = y + D * k by linarith, e_periodic hD]

/-- Scaling: `e_{gE}(g y) = e_E(y)`. -/
theorem e_scale {g E : ℕ} (hg : 0 < g) (y : ℤ) : e (g * E) (g * y) = e E y := by
  unfold e
  congr 1
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  push_cast
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp
  · have hE' : (E : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
    field_simp

/-- `e_1 ≡ 1`. -/
theorem e_one (x : ℤ) : e 1 x = 1 := by
  have := e_mul_self (D := 1) one_pos x
  simpa using this

/-- Inverses modulo `D` reduce to inverses modulo any divisor, and are unique there. -/
theorem inverse_reduces {D E : ℕ} (hED : E ∣ D) {z zi zi' : ℤ} (hzi : z * zi ≡ 1 [ZMOD D])
    (hzi' : z * zi' ≡ 1 [ZMOD E]) : zi ≡ zi' [ZMOD E] := by
  have h1 : z * zi ≡ 1 [ZMOD E] := Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hED) hzi
  calc zi = zi * 1 := by ring
    _ ≡ zi * (z * zi') [ZMOD E] := (Int.ModEq.mul_left _ hzi'.symm)
    _ = zi' * (z * zi) := by ring
    _ ≡ zi' * 1 [ZMOD E] := Int.ModEq.mul_left _ h1
    _ = zi' := by ring

/-- **The colour-conductor reduction** (`c` need not be a unit mod `D`). -/
theorem colour_conductor_reduction {D c : ℕ} (hD : 0 < D) (h z zi zi' : ℤ)
    (hzi : z * zi ≡ 1 [ZMOD D]) (hzi' : z * zi' ≡ 1 [ZMOD ((D / Nat.gcd D c : ℕ) : ℤ)]) :
    e D (h * c * zi) = e (D / Nat.gcd D c) (h * (c / Nat.gcd D c : ℕ) * zi') := by
  set g := Nat.gcd D c with hg
  set E := D / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hD
  have hDg : D = g * E := (Nat.mul_div_cancel' (Nat.gcd_dvd_left D c)).symm
  have hcg : (c : ℤ) = g * ((c / g : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right D c)]
  have hEpos : 0 < E := Nat.div_pos (Nat.le_of_dvd hD (Nat.gcd_dvd_left D c)) hgpos
  have hED : E ∣ D := ⟨g, by rw [hDg, mul_comm]⟩
  have step1 : e D (h * c * zi) = e E (h * (c / g : ℕ) * zi) := by
    rw [hcg, show h * (g * ((c / g : ℕ) : ℤ)) * zi = g * (h * (c / g : ℕ) * zi) by ring]
    conv_lhs => rw [hDg]
    exact e_scale hgpos _
  rw [step1]
  exact e_congr hEpos (Int.ModEq.mul_left _ (inverse_reduces hED hzi hzi'))

/-- **Degenerate case `E = 1`** (`D ∣ c`): the phase is identically `1`. -/
theorem colour_conductor_E_one {D c : ℕ} (hD : 0 < D) (hDc : D ∣ c)
    (h z zi : ℤ) (hzi : z * zi ≡ 1 [ZMOD D]) : e D (h * c * zi) = 1 := by
  have hE : D / Nat.gcd D c = 1 := by
    rw [Nat.gcd_eq_left hDc, Nat.div_self hD]
  have := colour_conductor_reduction hD h z zi 0 hzi (by rw [hE]; exact Int.modEq_one)
  rw [this, hE, e_one]

/-- **Fixture:** `D = 6`, `c = 4` (not a unit mod `6`): `g = 2`, `E = 3`, `c₀ = 2`. -/
theorem nonunit_fixture :
    Nat.gcd 6 4 = 2 ∧ 6 / Nat.gcd 6 4 = 3 ∧ 4 / Nat.gcd 6 4 = 2 ∧ ¬ Nat.Coprime 4 6 := by
  decide

end ColourConductor
end ResearchBankV18
end Erdos287
