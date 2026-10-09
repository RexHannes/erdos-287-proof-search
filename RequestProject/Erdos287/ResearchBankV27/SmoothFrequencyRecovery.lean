import Mathlib

/-!
# Erdős #287 — Research Bank V27 §7: smooth frequency recovery

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**LEAN BANK** (exact algebra, all inverse-existence hypotheses explicit):
* `reciprocity_dvd` — if `a ā ≡ 1 (mod b)`, `b b̄ ≡ 1 (mod a)` and `(a, b) = 1`, then
  `ab ∣ a ā + b b̄ − 1`;
* `reciprocity_frac` — hence `c ā / b + c b̄ / a − c / (ab) ∈ ℤ` for every integer `c`; with
  `c = a₀ f`, `a = n₁ r₂`, `b = n₂ r₁`, this is the reciprocity step
  `m_{a₀}/L ≡ a₀ f \overline{n₂ r₁}/(n₁ r₂) + a₀/(L n₁) (mod 1)` once the (explicit) relation
  between `m_{a₀}`, `L` and the inverses is substituted (`reciprocity_instance`).
* `fixed_J_exists` / `frequency_tail_absorbed` — a FIXED `J` (chosen before `x → ∞`) makes the
  Schwartz tail beyond `H_cap` absorb any fixed polynomial outer count `x^P` and still save `x^{-A}`.
* `colour_partial_summation` — Abel summation in which the colour coefficients stay INSIDE the
  partial sums and only the smooth physical weight is differenced.
* `real_correction_exponent_facts` — the supplied real-correction exponent `−1079/1900` is
  negative, beats `−1/2` and beats `−η` for `η = 1/1100` (rational arithmetic).

**EXTERNAL PROVIDER** (never constructed):
* `SchwartzFrequencyProvider` — `Σ_{0<|h|≤H} |h| |ψ̂(h/t)| ≤ C_ψ t²`;
* `FrequencyCapProvider` — for a fixed `J > 2`, the tail `Σ_{H_cap<|h|≤H} |ψ̂(hM/L)| ≤
  C_{ψ,J} (L/M) x^{−(J−1)η/4}`, with `H_cap = C Q d R² S² / M · x^{η/4}` (no exponential decay
  is claimed for compactly supported smooth weights);
* `SmoothRecoveryProvider` — the variation bound `Σ_n |b_{n+1} − b_n| ≤ V` for the physical
  smooth cutoff.

The derivation of the literal exponent `1079/1900` from the analytic real-correction estimate is
NOT reconstructed here: it is recorded as the supplied value, and only its rational arithmetic is
kernel-checked.
-/

namespace Erdos287
namespace ResearchBankV27
namespace SmoothFrequencyRecovery

open Finset

/-- **Reciprocity divisibility** (LEAN BANK). -/
theorem reciprocity_dvd {a b abar bbar : ℤ} (hab : IsCoprime a b) (ha : b ∣ a * abar - 1)
    (hb : a ∣ b * bbar - 1) : a * b ∣ a * abar + b * bbar - 1 := by
  have h1 : a ∣ a * abar + b * bbar - 1 := by
    have : a * abar + b * bbar - 1 = a * abar + (b * bbar - 1) := by ring
    rw [this]; exact dvd_add (dvd_mul_right _ _) hb
  have h2 : b ∣ a * abar + b * bbar - 1 := by
    have : a * abar + b * bbar - 1 = (a * abar - 1) + b * bbar := by ring
    rw [this]; exact dvd_add ha (dvd_mul_right _ _)
  exact hab.mul_dvd h1 h2

/-- **Fractional reciprocity** (LEAN BANK): `c ā/b + c b̄/a − c/(ab) ∈ ℤ`. -/
theorem reciprocity_frac {a b abar bbar : ℤ} (hab : IsCoprime a b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : b ∣ a * abar - 1) (hb : a ∣ b * bbar - 1) (c : ℤ) :
    ∃ k : ℤ, (c * abar : ℚ) / b + (c * bbar : ℚ) / a - (c : ℚ) / (a * b) = k := by
  obtain ⟨k, hk⟩ := reciprocity_dvd hab ha hb
  refine ⟨c * k, ?_⟩
  have hk' : ((a : ℚ) * abar + b * bbar - 1) = a * b * k := by exact_mod_cast hk
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha0
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  field_simp
  push_cast
  linear_combination (c : ℚ) * hk'

/-- **Reciprocity instance** (LEAN BANK): if `m/L = c ā/b + e` for a rational `e` (the explicit
substitution of the inverse `ā = \overline{n₂ r₁}` etc.), then modulo `1`,
`m/L ≡ −c b̄/a + c/(ab) + e`. -/
theorem reciprocity_instance {a b abar bbar : ℤ} (hab : IsCoprime a b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (ha : b ∣ a * abar - 1) (hb : a ∣ b * bbar - 1) (c : ℤ) {m L e : ℚ}
    (hm : m / L = (c * abar : ℚ) / b + e) :
    ∃ k : ℤ, m / L = -((c * bbar : ℚ) / a) + (c : ℚ) / (a * b) + e + k := by
  obtain ⟨k, hk⟩ := reciprocity_frac hab ha0 hb0 ha hb c
  exact ⟨k, by rw [hm]; linarith⟩

/-- **Schwartz frequency provider** (EXTERNAL PROVIDER; never constructed). -/
structure SchwartzFrequencyProvider (psiHat : ℝ → ℝ) (C : ℝ) : Prop where
  bound : ∀ (t : ℝ), 1 ≤ t → ∀ H : ℕ,
    ∑ h ∈ Finset.Icc (1 : ℤ) H, (|(h : ℝ)| * |psiHat (h / t)| + |(h : ℝ)| * |psiHat (-h / t)|) ≤
      C * t ^ 2

/-- The real-correction error bound supplied by the Schwartz provider (LEAN CONDITIONAL):
the correction `Σ_h |h| |ψ̂(h/t)| · amp` is at most `C t² · amp`. -/
theorem real_correction_conditional {psiHat : ℝ → ℝ} {C : ℝ}
    (hS : SchwartzFrequencyProvider psiHat C) {t amp : ℝ} (ht : 1 ≤ t) (hamp : 0 ≤ amp) (H : ℕ) :
    (∑ h ∈ Finset.Icc (1 : ℤ) H,
        (|(h : ℝ)| * |psiHat (h / t)| + |(h : ℝ)| * |psiHat (-h / t)|)) * amp ≤
      C * t ^ 2 * amp :=
  mul_le_mul_of_nonneg_right (hS.bound t ht H) hamp

/-- The supplied real-correction exponent. -/
def realCorrectionExponent : ℚ := -1079 / 1900

/-- Rational facts about the supplied real-correction exponent (LEAN BANK). -/
theorem real_correction_exponent_facts :
    realCorrectionExponent < 0 ∧ realCorrectionExponent < -1 / 2 ∧
      realCorrectionExponent < -(1 / 1100) ∧ realCorrectionExponent = -1 / 2 - 129 / 1900 := by
  unfold realCorrectionExponent; norm_num

/-- The frequency cap `H_cap = C Q d R² S² / M · x^{η/4}`. -/
noncomputable def Hcap (C Q d R S M x η : ℝ) : ℝ := C * Q * d * R ^ 2 * S ^ 2 / M * x ^ (η / 4)

/-- **Frequency-cap (Schwartz tail) provider** (EXTERNAL PROVIDER; never constructed). For a FIXED
`J > 2`, the tail beyond `H_cap` is `≤ C_{ψ,J} (L/M) x^{−(J−1)η/4}`. -/
structure FrequencyCapProvider (psiHat : ℝ → ℝ) (J : ℕ) (CJ C Q d R S M L x η : ℝ) : Prop where
  J_gt : 2 < J
  tail : ∀ H : ℕ,
    ∑ h ∈ (Finset.Icc (1 : ℤ) H).filter (fun h : ℤ => Hcap C Q d R S M x η < (h : ℝ)),
        (|psiHat (h * M / L)| + |psiHat (-h * M / L)|) ≤
      CJ * (L / M) * x ^ (-((J : ℝ) - 1) * η / 4)

/-- **A fixed `J` exists** (LEAN BANK): for any fixed polynomial outer exponent `P ≥ 0` and saving
`A ≥ 0`, there is a natural `J > 2`, independent of `x`, with `(J−1)η/4 ≥ P + A`. -/
theorem fixed_J_exists {η : ℝ} (hη : 0 < η) (P A : ℝ) :
    ∃ J : ℕ, 2 < J ∧ P + A ≤ ((J : ℝ) - 1) * η / 4 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (P + A) / η)
  refine ⟨n + 3, by omega, ?_⟩
  have : 4 * (P + A) / η * η = 4 * (P + A) := div_mul_cancel₀ _ hη.ne'
  push_cast
  nlinarith

/-- **Tail absorption** (LEAN BANK): an outer count `≤ x^P` times the tail `x^{−(J−1)η/4}` is at
most `x^{−A}` once `(J−1)η/4 ≥ P + A`. -/
theorem frequency_tail_absorbed {x P A η : ℝ} {J : ℕ} (hx : 1 ≤ x)
    (hJ : P + A ≤ ((J : ℝ) - 1) * η / 4) :
    x ^ P * x ^ (-((J : ℝ) - 1) * η / 4) ≤ x ^ (-A) := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- **Frequency cap, conditional** (LEAN CONDITIONAL on `FrequencyCapProvider`): an outer count
`≤ x^P` times the Schwartz tail beyond `H_cap` is `≤ C_{ψ,J} (L/M) x^{−A}` for the fixed `J`. -/
theorem frequency_cap_conditional {psiHat : ℝ → ℝ} {J : ℕ} {CJ C Q d R S M L x η P A cnt : ℝ}
    (hF : FrequencyCapProvider psiHat J CJ C Q d R S M L x η) (hx : 1 ≤ x)
    (hJ : P + A ≤ ((J : ℝ) - 1) * η / 4) (hcnt : cnt ≤ x ^ P)
    (hCLM : 0 ≤ CJ * (L / M)) (H : ℕ) :
    cnt * ∑ h ∈ (Finset.Icc (1 : ℤ) H).filter (fun h : ℤ => Hcap C Q d R S M x η < (h : ℝ)),
        (|psiHat (h * M / L)| + |psiHat (-h * M / L)|) ≤ CJ * (L / M) * x ^ (-A) := by
  have hx0 : 0 < x := by linarith
  calc _ ≤ x ^ P * (CJ * (L / M) * x ^ (-((J : ℝ) - 1) * η / 4)) :=
        mul_le_mul hcnt (hF.tail H)
          (Finset.sum_nonneg fun _ _ => by positivity) (Real.rpow_nonneg hx0.le _)
    _ = CJ * (L / M) * (x ^ P * x ^ (-((J : ℝ) - 1) * η / 4)) := by ring
    _ ≤ CJ * (L / M) * x ^ (-A) :=
        mul_le_mul_of_nonneg_left (frequency_tail_absorbed hx hJ) hCLM

/-- **Smooth-recovery (variation) provider** (EXTERNAL PROVIDER; never constructed). -/
structure SmoothRecoveryProvider (b : ℕ → ℝ) (n : ℕ) (V : ℝ) : Prop where
  variation : ∑ i ∈ range (n - 1), |b (i + 1) - b i| ≤ V

/-- **Colour partial summation** (LEAN BANK): the colour coefficients `a` stay inside partial
sums `A_i = Σ_{k≤i} a_k`; only the smooth weight `b` is differenced. -/
theorem colour_partial_summation (a : ℕ → ℂ) (b : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (b i : ℂ) * a i =
      (b (n - 1) : ℂ) * ∑ i ∈ range n, a i -
        ∑ i ∈ range (n - 1), ((b (i + 1) : ℂ) - b i) * ∑ k ∈ range (i + 1), a k := by
  have := Finset.sum_range_by_parts (fun i => (b i : ℂ)) a n
  simpa [smul_eq_mul] using this

/-- **Conditional smooth recovery** (LEAN CONDITIONAL on `SmoothRecoveryProvider`): if every colour
partial sum is bounded by `Amax`, then `|Σ b_i a_i| ≤ Amax (|b_{n−1}| + V)`. -/
theorem smooth_recovery_conditional (a : ℕ → ℂ) (b : ℕ → ℝ) (n : ℕ) {V Amax : ℝ}
    (hV : SmoothRecoveryProvider b n V) (hA : ∀ i, ‖∑ k ∈ range (i + 1), a k‖ ≤ Amax)
    (hAn : ‖∑ k ∈ range n, a k‖ ≤ Amax) (hA0 : 0 ≤ Amax) :
    ‖∑ i ∈ range n, (b i : ℂ) * a i‖ ≤ Amax * (|b (n - 1)| + V) := by
  rw [colour_partial_summation]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(b (n - 1) : ℂ) * ∑ i ∈ range n, a i‖ ≤ |b (n - 1)| * Amax := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hAn (abs_nonneg _)
  have h2 : ‖∑ i ∈ range (n - 1), ((b (i + 1) : ℂ) - b i) * ∑ k ∈ range (i + 1), a k‖ ≤
      (∑ i ∈ range (n - 1), |b (i + 1) - b i|) * Amax := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)
  have h3 := mul_le_mul_of_nonneg_right hV.variation hA0
  nlinarith

end SmoothFrequencyRecovery
end ResearchBankV27
end Erdos287
