import RequestProject.Erdos287.ResearchBankV18.ColourConductor

/-!
# Erdős #287 — Research Bank V19 §4: prime powers / overlap CRT reduction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For arbitrary positive `D, s`: `g = gcd(D, s)`, `D₁ = D/g`, `s₁ = s/g`.

Kernel-proved (LEAN BANK), for ALL positive `D, s` (so prime powers and overlapping
valuations are covered; no squarefreeness or coprimality is assumed):
* `coprime_D1_s1` — `gcd(D₁, s₁) = 1`;
* `lcm_eq` — `lcm(D, s) = g · D₁ · s₁`;
* **`crt_phase_reduction`** — for compatible roots with `b − a = g c` and a CRT difference `Δ`
  with `Δ ≡ 0 (mod s)`, `Δ ≡ b − a (mod D)`, and `s̄₁` an inverse of `s₁` mod `D₁`:
  `e_{[D,s]}(h Δ) = e_{D₁}(h c s̄₁)`;
* `IsPeriod`, `period_of_dvd` — `D₁ / gcd(D₁, c)` is an additive period of `h ↦ e_{D₁}(h c s̄₁)`;
* `leastPeriod_dvd` — the least positive period (primitive additive conductor) divides every
  positive period; hence **`conductor_dvd`**: the primitive conductor divides `D₁ / gcd(D₁, c)`;
* `prime_power_fixture` — `D = 8 = 2³`, `s = 12 = 2²·3`: `g = 4`, `D₁ = 2`, `s₁ = 3`.
-/

namespace Erdos287
namespace ResearchBankV19
namespace PrimePowerCRT

open ResearchBankV18.ColourConductor

theorem coprime_D1_s1 {D s : ℕ} (hD : 0 < D) :
    Nat.Coprime (D / Nat.gcd D s) (s / Nat.gcd D s) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hD)

theorem lcm_eq {D s : ℕ} (hD : 0 < D) :
    Nat.lcm D s = Nat.gcd D s * (D / Nat.gcd D s) * (s / Nat.gcd D s) := by
  have hg := Nat.gcd_pos_of_pos_left s hD
  have h1 : Nat.gcd D s * (D / Nat.gcd D s) = D := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  rw [h1, Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]

/-- **The exact overlap CRT phase reduction.** -/
theorem crt_phase_reduction {D s : ℕ} (hD : 0 < D) (hs : 0 < s) {a b c Δ s1i h : ℤ}
    (hba : b - a = (Nat.gcd D s : ℤ) * c) (hΔs : Δ ≡ 0 [ZMOD s]) (hΔD : Δ ≡ b - a [ZMOD D])
    (hinv : ((s / Nat.gcd D s : ℕ) : ℤ) * s1i ≡ 1 [ZMOD ((D / Nat.gcd D s : ℕ) : ℤ)]) :
    e (Nat.lcm D s) (h * Δ) = e (D / Nat.gcd D s) (h * c * s1i) := by
  set g := Nat.gcd D s
  set D₁ := D / g
  set s₁ := s / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s hD
  have hDg : (D : ℤ) = g * D₁ := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left D s)).symm
  have hsg : (s : ℤ) = g * s₁ := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right D s)).symm
  have hD1 : 0 < D₁ := Nat.div_pos (Nat.le_of_dvd hD (Nat.gcd_dvd_left D s)) hg
  have hs1 : 0 < s₁ := Nat.div_pos (Nat.le_of_dvd hs (Nat.gcd_dvd_right D s)) hg
  obtain ⟨t, ht⟩ : (s : ℤ) ∣ Δ := by
    have := Int.modEq_iff_dvd.1 hΔs; simpa using this
  -- `s₁ t ≡ c (mod D₁)`
  have key : (s₁ : ℤ) * t ≡ c [ZMOD D₁] := by
    have h1 := Int.modEq_iff_dvd.1 hΔD
    rw [ht, hba, hsg, hDg] at h1
    obtain ⟨k, hk⟩ := h1
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    apply Int.modEq_iff_dvd.2
    refine ⟨k, ?_⟩
    have : (g : ℤ) * (c - s₁ * t) = g * (D₁ * k) := by linarith
    have := mul_left_cancel₀ hg0 this
    linarith
  have ht' : t ≡ c * s1i [ZMOD D₁] := by
    calc t = t * 1 := by ring
      _ ≡ t * (s₁ * s1i) [ZMOD D₁] := Int.ModEq.mul_left _ hinv.symm
      _ = (s₁ * t) * s1i := by ring
      _ ≡ c * s1i [ZMOD D₁] := Int.ModEq.mul_right _ key
  rw [lcm_eq hD, ht, hsg]
  have hsc : ((g : ℕ) : ℤ) * (s₁ : ℤ) = ((g * s₁ : ℕ) : ℤ) := by push_cast; ring
  rw [show h * ((g : ℤ) * s₁ * t) = ((g * s₁ : ℕ) : ℤ) * (h * t) by push_cast; ring,
    show g * D₁ * s₁ = (g * s₁) * D₁ by ring]
  rw [e_scale (Nat.mul_pos hg hs1)]
  apply e_congr hD1
  calc h * t ≡ h * (c * s1i) [ZMOD D₁] := Int.ModEq.mul_left _ ht'
    _ = h * c * s1i := by ring

/-- An additive period of a function on `ℤ`. -/
def IsPeriod (f : ℤ → ℂ) (p : ℕ) : Prop := ∀ h, f (h + p) = f h

theorem IsPeriod.mul {f : ℤ → ℂ} {p : ℕ} (hp : IsPeriod f p) (k : ℕ) : ∀ h, f (h + k * p) = f h := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    rw [show h + ((k + 1 : ℕ) : ℤ) * p = (h + k * p) + p by push_cast; ring, hp, ih]

/-- `D₁ / gcd(D₁, c)` is a period of `h ↦ e_{D₁}(h c s̄₁)`. -/
theorem period_of_dvd {D₁ : ℕ} (hD₁ : 0 < D₁) (c s1i : ℤ) :
    IsPeriod (fun h => e D₁ (h * c * s1i)) (D₁ / Nat.gcd D₁ c.natAbs) := by
  intro h
  set p := D₁ / Nat.gcd D₁ c.natAbs
  have hdiv : (D₁ : ℤ) ∣ (p : ℤ) * c := by
    have h1 : (Nat.gcd D₁ c.natAbs : ℤ) ∣ c := by
      have := Int.natCast_dvd.2 (Nat.gcd_dvd_right D₁ c.natAbs); simpa using this
    obtain ⟨c', hc'⟩ := h1
    have hp : (D₁ : ℤ) = Nat.gcd D₁ c.natAbs * p := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left D₁ c.natAbs)).symm
    refine ⟨c', ?_⟩
    rw [hc', hp]; ring
  obtain ⟨k, hk⟩ := hdiv
  show e D₁ ((h + p) * c * s1i) = e D₁ (h * c * s1i)
  rw [show (h + p) * c * s1i = h * c * s1i + D₁ * (k * s1i) by
    rw [add_mul, add_mul, hk]; ring]
  exact e_periodic hD₁ _ _

theorem IsPeriod.neg {f : ℤ → ℂ} {p : ℕ} (hp : IsPeriod f p) : ∀ h, f (h - p) = f h := by
  intro h; rw [← hp (h - p), sub_add_cancel]

theorem IsPeriod.mod {f : ℤ → ℂ} {p q : ℕ} (hp : IsPeriod f p) (hq : IsPeriod f q) :
    IsPeriod f (p % q) := by
  intro h
  have e1 : ((p % q : ℕ) : ℤ) = p - (p / q : ℕ) * q := by
    have h0 := Nat.mod_add_div p q
    have h1 : ((p % q : ℕ) : ℤ) + (q : ℤ) * ((p / q : ℕ) : ℤ) = p := by exact_mod_cast h0
    linarith
  rw [e1]
  have hneg : ∀ k : ℕ, ∀ h, f (h - k * q) = f h := by
    intro k h
    have := hq.mul k (h - k * q)
    rw [sub_add_cancel] at this; exact this.symm
  rw [show h + (p - (p / q : ℕ) * q) = (h + p) - (p / q : ℕ) * q by ring, hneg, hp]

/-- **The least positive period divides every positive period.** -/
theorem leastPeriod_dvd {f : ℤ → ℂ} {p₀ p : ℕ} (hp₀ : 0 < p₀) (hper₀ : IsPeriod f p₀)
    (hmin : ∀ q, 0 < q → IsPeriod f q → p₀ ≤ q) (hper : IsPeriod f p) : p₀ ∣ p := by
  by_contra hnd
  have hpos : 0 < p % p₀ := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have := hmin _ hpos (hper.mod hper₀)
  have := Nat.mod_lt p hp₀
  omega

/-- **The primitive additive conductor divides `D₁ / gcd(D₁, c)`.** -/
theorem conductor_dvd {D₁ : ℕ} (hD₁ : 0 < D₁) (c s1i : ℤ) {p₀ : ℕ} (hp₀ : 0 < p₀)
    (hper₀ : IsPeriod (fun h => e D₁ (h * c * s1i)) p₀)
    (hmin : ∀ q, 0 < q → IsPeriod (fun h => e D₁ (h * c * s1i)) q → p₀ ≤ q) :
    p₀ ∣ D₁ / Nat.gcd D₁ c.natAbs :=
  leastPeriod_dvd hp₀ hper₀ hmin (period_of_dvd hD₁ c s1i)

/-- Prime-power / overlap fixture. -/
theorem prime_power_fixture :
    Nat.gcd 8 12 = 4 ∧ 8 / Nat.gcd 8 12 = 2 ∧ 12 / Nat.gcd 8 12 = 3 ∧
      Nat.Coprime (8 / Nat.gcd 8 12) (12 / Nat.gcd 8 12) ∧ Nat.lcm 8 12 = 4 * 2 * 3 := by
  decide

end PrimePowerCRT
end ResearchBankV19
end Erdos287
