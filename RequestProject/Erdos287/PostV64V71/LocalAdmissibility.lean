import Mathlib

/-!
# Erdős #287 — V71 local admissibility and exact local singular factors

**Status: BANK (LEAN PROVED)** for all exact local statements.  The averaged singular-series
asymptotic is **not** proved (see `AnalyticFrontier.lean`, `AverageSingularSeries287`).

For a genuine prime determinant tuple `k q - t r = ε`, `ε = ±1`, `q, r` odd primes:

* `local_determinant_admissibility` — `gcd(k, t) = 1`, `k + t` odd (i.e. `k - t` odd), `q ≠ r`;
* `exists_bezout_det` — for coprime `k, t` there are `a, b` with `k a - t b = ε`;
* `determinant_parametrisation` — every solution is `q = t u + a`, `r = k u + b`;
* `no_common_root` — resultant argument: `t u + a` and `k u + b` have no common root mod `ℓ`;
* `local_forbidden_residue_count` — for every prime `ℓ`, the number of `u mod ℓ` with
  `ℓ ∣ (t u + a)(k u + b)` is `1` if `ℓ ∣ k t` and `2` otherwise;
* `parity_collapse` — if `k + t` is odd then `2 ∣ k t`, so `ν₂ = 1`;
* `local_factor_ratio` — `[(1 - 1/ℓ)/(1 - 1/ℓ)²] / [(1 - 2/ℓ)/(1 - 1/ℓ)²] = (ℓ - 1)/(ℓ - 2)`;
* `singularLocal`, `singularSeries` — the exact local product `∏_{ℓ ∣ kt, ℓ > 2} (ℓ-1)/(ℓ-2)`
  and `S(k,t) = 2 C₂ ∏ …` on admissible pairs (`C₂` is a parameter; no convergence is claimed).
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

/-- **Local admissibility of a genuine prime determinant tuple.** -/
theorem local_determinant_admissibility {k t q r : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hdet : (k : ℤ) * q - (t : ℤ) * r = ε) (hq : q.Prime) (hr : r.Prime) (hq2 : q ≠ 2)
    (hr2 : r ≠ 2) : Nat.Coprime k t ∧ Odd (k + t) ∧ q ≠ r := by
  refine ⟨?_, ?_, ?_⟩
  · -- a common divisor divides `ε = ±1`
    set d := Nat.gcd k t
    have hdk : (d : ℤ) ∣ k := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left k t)
    have hdt : (d : ℤ) ∣ t := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right k t)
    have hdε : (d : ℤ) ∣ ε := hdet ▸ dvd_sub (dvd_mul_of_dvd_left hdk _) (dvd_mul_of_dvd_left hdt _)
    have : d ∣ 1 := by
      have := Int.natAbs_dvd_natAbs.2 hdε
      rcases hε with rfl | rfl <;> simpa using this
    exact Nat.dvd_one.1 this
  · -- parity
    have hqo : Odd (q : ℤ) := by exact_mod_cast hq.odd_of_ne_two hq2
    have hro : Odd (r : ℤ) := by exact_mod_cast hr.odd_of_ne_two hr2
    have hεo : Odd ε := by rcases hε with rfl | rfl <;> decide
    rw [← hdet] at hεo
    have : Odd ((k : ℤ) + t) := by
      rw [Int.odd_sub, Int.odd_mul, Int.even_mul] at hεo
      rw [Int.odd_add]
      have hre : ¬ Even (r : ℤ) := Int.not_even_iff_odd.2 hro
      tauto
    exact_mod_cast this
  · rintro rfl
    have h : ((k : ℤ) - t) * q = ε := by rw [← hdet]; ring
    have hdvd : (q : ℤ) ∣ ε := ⟨(k : ℤ) - t, by rw [← h]; ring⟩
    have : q ∣ 1 := by
      have := Int.natAbs_dvd_natAbs.2 hdvd
      rcases hε with rfl | rfl <;> simpa using this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)

/-- **Bézout for the determinant**: coprime `k, t` admit `a, b` with `k a - t b = ε`. -/
theorem exists_bezout_det {k t : ℕ} (hkt : Nat.Coprime k t) (ε : ℤ) :
    ∃ a b : ℤ, (k : ℤ) * a - (t : ℤ) * b = ε := by
  have h := Int.gcd_eq_gcd_ab (k : ℤ) (t : ℤ)
  have hg : Int.gcd (k : ℤ) (t : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact hkt
  rw [hg] at h
  refine ⟨ε * Int.gcdA k t, -(ε * Int.gcdB k t), ?_⟩
  have : (1 : ℤ) = k * Int.gcdA k t + t * Int.gcdB k t := by exact_mod_cast h
  linear_combination (-ε) * this

/-- **Determinant parametrisation**: if `k a - t b = ε` and `k q - t r = ε` with `gcd(k,t) = 1`,
`t ≠ 0`, then `q = t u + a`, `r = k u + b` for some `u ∈ ℤ`. -/
theorem determinant_parametrisation {k t : ℕ} (hkt : Nat.Coprime k t) (ht : t ≠ 0)
    {a b q r ε : ℤ} (hab : (k : ℤ) * a - (t : ℤ) * b = ε) (hqr : (k : ℤ) * q - (t : ℤ) * r = ε) :
    ∃ u : ℤ, q = t * u + a ∧ r = k * u + b := by
  have hkey : (k : ℤ) * (q - a) = t * (r - b) := by linear_combination hqr - hab
  have hcop : IsCoprime (t : ℤ) (k : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hkt.symm
  have htdvd : (t : ℤ) ∣ (q - a) := hcop.dvd_of_dvd_mul_left ⟨r - b, by rw [← hkey]⟩
  obtain ⟨u, hu⟩ := htdvd
  refine ⟨u, by linarith, ?_⟩
  have ht0 : (t : ℤ) ≠ 0 := by exact_mod_cast ht
  have : (t : ℤ) * (r - b) = t * (k * u) := by rw [← hkey, hu]; ring
  have := mul_left_cancel₀ ht0 this
  linarith

/-- **No common root (resultant argument).**  Modulo a prime `ℓ`, `t u + a` and `k u + b` have no
common root when `k a - t b = ±1`. -/
theorem no_common_root (ℓ : ℕ) [Fact ℓ.Prime] {k t : ℕ} {a b ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hdet : (k : ℤ) * a - (t : ℤ) * b = ε) (u : ZMod ℓ) :
    ¬ ((t : ZMod ℓ) * u + a = 0 ∧ (k : ZMod ℓ) * u + b = 0) := by
  rintro ⟨h1, h2⟩
  have hres : (k : ZMod ℓ) * ((t : ZMod ℓ) * u + a) - (t : ZMod ℓ) * ((k : ZMod ℓ) * u + b) =
      (ε : ZMod ℓ) := by
    have : ((k : ℤ) * a - (t : ℤ) * b : ℤ) = ε := hdet
    have h' := congrArg (fun z : ℤ => (z : ZMod ℓ)) this
    push_cast at h'
    rw [← h']; ring
  rw [h1, h2] at hres
  simp only [mul_zero, sub_zero] at hres
  rcases hε with rfl | rfl
  · simp at hres
  · simp at hres

/-- **Local forbidden-residue count.**  For a prime `ℓ` and `k a - t b = ±1`,
`#{u mod ℓ : (t u + a)(k u + b) ≡ 0} = 1` if `ℓ ∣ k t`, and `= 2` otherwise. -/
theorem local_forbidden_residue_count (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {k t : ℕ} {a b ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hdet : (k : ℤ) * a - (t : ℤ) * b = ε) :
    (Finset.univ.filter (fun u : ZMod ℓ =>
      ((t : ZMod ℓ) * u + a) * ((k : ZMod ℓ) * u + b) = 0)).card =
      if ℓ ∣ k * t then 1 else 2 := by
  have hdetZ : (k : ZMod ℓ) * a - (t : ZMod ℓ) * b = ε := by
    have h' := congrArg (fun z : ℤ => (z : ZMod ℓ)) hdet
    push_cast at h'; exact h'
  have hε0 : (ε : ZMod ℓ) ≠ 0 := by
    rcases hε with rfl | rfl <;> simp
  split_ifs with hdvd
  · rcases (Nat.Prime.dvd_mul hℓ.out).1 hdvd with hk | ht
    · -- `ℓ ∣ k`: second factor is the nonzero constant `b`
      have hk0 : (k : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff k ℓ).2 hk
      rw [hk0, zero_mul, zero_sub] at hdetZ
      have ht0 : (t : ZMod ℓ) ≠ 0 := fun h => hε0 (by rw [← hdetZ, h]; ring)
      have hb0 : (b : ZMod ℓ) ≠ 0 := fun h => hε0 (by rw [← hdetZ, h]; ring)
      rw [Finset.card_eq_one]
      refine ⟨-(a : ZMod ℓ) / t, ?_⟩
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hk0,
        zero_mul, zero_add, mul_eq_zero, hb0, or_false]
      constructor
      · intro h; field_simp; linear_combination h
      · intro h; rw [h]; field_simp; ring
    · -- `ℓ ∣ t`: first factor is the nonzero constant `a`
      have ht0 : (t : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff t ℓ).2 ht
      rw [ht0, zero_mul, sub_zero] at hdetZ
      have hk0 : (k : ZMod ℓ) ≠ 0 := fun h => hε0 (by rw [← hdetZ, h]; ring)
      have ha0 : (a : ZMod ℓ) ≠ 0 := fun h => hε0 (by rw [← hdetZ, h]; ring)
      rw [Finset.card_eq_one]
      refine ⟨-(b : ZMod ℓ) / k, ?_⟩
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ht0,
        zero_mul, zero_add, mul_eq_zero, ha0, false_or]
      constructor
      · intro h; field_simp; linear_combination h
      · intro h; rw [h]; field_simp; ring
  · -- `ℓ ∤ k t`: two distinct roots
    have hk0 : (k : ZMod ℓ) ≠ 0 := fun h =>
      hdvd (dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff k ℓ).1 h) t)
    have ht0 : (t : ZMod ℓ) ≠ 0 := fun h =>
      hdvd (dvd_mul_of_dvd_right ((ZMod.natCast_eq_zero_iff t ℓ).1 h) k)
    have hne : -(a : ZMod ℓ) / t ≠ -(b : ZMod ℓ) / k := by
      intro h
      apply hε0
      rw [← hdetZ]
      field_simp at h
      linear_combination -h
    rw [Finset.card_eq_two]
    refine ⟨-(a : ZMod ℓ) / t, -(b : ZMod ℓ) / k, hne, ?_⟩
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero]
    constructor
    · rintro (h | h)
      · left; field_simp; linear_combination h
      · right; field_simp; linear_combination h
    · rintro (h | h)
      · left; rw [h]; field_simp; ring
      · right; rw [h]; field_simp; ring

/-- **Parity collapse at `ℓ = 2`**: if `k + t` is odd then `2 ∣ k t` (so `ν₂ = 1`). -/
theorem parity_collapse {k t : ℕ} (h : Odd (k + t)) : 2 ∣ k * t := by
  rw [Nat.odd_add] at h
  rcases Nat.even_or_odd k with hk | hk
  · exact dvd_mul_of_dvd_left (even_iff_two_dvd.1 hk) t
  · have : Even t := by
      by_contra ht; rw [Nat.not_even_iff_odd] at ht; exact absurd (h.1 hk) (Nat.not_even_iff_odd.2 ht)
    exact dvd_mul_of_dvd_right (even_iff_two_dvd.1 this) k

/-! ## Exact local singular factors -/

/-- The local density factor `(1 - ν/ℓ)/(1 - 1/ℓ)²`. -/
noncomputable def localDensity (ν ℓ : ℝ) : ℝ := (1 - ν / ℓ) / (1 - 1 / ℓ) ^ 2

/-- **Local factor ratio**: for `ℓ > 2`, `localDensity 1 ℓ / localDensity 2 ℓ = (ℓ-1)/(ℓ-2)`. -/
theorem local_factor_ratio {ℓ : ℝ} (hℓ : 2 < ℓ) :
    localDensity 1 ℓ / localDensity 2 ℓ = (ℓ - 1) / (ℓ - 2) := by
  unfold localDensity
  have h0 : ℓ ≠ 0 := by linarith
  have h1 : ℓ - 1 ≠ 0 := by linarith
  have h2 : ℓ - 2 ≠ 0 := by linarith
  field_simp

/-- The exact local product `∏_{ℓ ∣ kt, ℓ > 2} (ℓ - 1)/(ℓ - 2)`. -/
noncomputable def singularLocal (k t : ℕ) : ℝ :=
  ∏ ℓ ∈ (k * t).primeFactors.filter (2 < ·), ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2)

/-- Admissibility of a pair `(k, t)`: coprime with `k + t` odd. -/
def AdmissiblePair (k t : ℕ) : Prop := Nat.Coprime k t ∧ Odd (k + t)

instance (k t : ℕ) : Decidable (AdmissiblePair k t) := by unfold AdmissiblePair; infer_instance

/-- `S(k, t) = 2 C₂ ∏_{ℓ ∣ kt, ℓ > 2} (ℓ-1)/(ℓ-2)` on admissible pairs and `0` otherwise
(`C₂` is a parameter; no convergence statement is made here). -/
noncomputable def singularSeries (C2 : ℝ) (k t : ℕ) : ℝ :=
  if AdmissiblePair k t then 2 * C2 * singularLocal k t else 0

theorem singularLocal_pos (k t : ℕ) : 0 < singularLocal k t := by
  unfold singularLocal
  refine Finset.prod_pos fun ℓ hℓ => ?_
  have h2 : (2 : ℝ) < ℓ := by exact_mod_cast (Finset.mem_filter.1 hℓ).2
  exact div_pos (by linarith) (by linarith)

end Erdos287.PostV64V71
