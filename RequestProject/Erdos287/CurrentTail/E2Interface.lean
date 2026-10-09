import RequestProject.Erdos287.CurrentTail.E1Interface

/-!
# Erdős #287 — current tail consolidation: the `E₂` (Pascadi-type) interface

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

## Source side (kernel-proved)

* `FixedLocalSplit`, `fixedLocal_totient`, `fixedLocal_bound` — the split `q = f · d`,
  `(f,d) = 1` of a modulus into fixed-local part and remaining part, with `φ(q) = φ(f)φ(d)` and
  the modulus bookkeeping `f ≤ F, d ≤ D ⟹ q ≤ FD`;
* `crt_phase_split` / `crt_phase_split_real` — the CRT phase identity: for coprime
  `q₁, q₂` with `u q₂ ≡ 1 (q₁)`, `v q₁ ≡ 1 (q₂)`:
  `a u/q₁ + a v/q₂ ≡ a/(q₁q₂) (mod 1)`;
* `dualLength`, `dualLength_enlarged` — Fourier-length enlargement: the dual length for
  modulus `f q` is `f` times that for `q`; `forgetting_enlargement_wrong` (regression);
* `kloostermanForm` — the spectral bilinear form with phases `cos(2π h r̄ / q)`;
  `kloostermanForm_split` — coefficient placement over a fixed-local split of the moduli.

## Analytic side (isolated, never constructed)

* `E2Hypotheses` — coefficient bounds, modulus ranges, Fourier length, coprimality and the
  parameter `T_H`, each as a separate field;
* `PascadiE2Printed δ` — the printed shape: for `T_H ≤ x^ε` (every fixed small `ε`) the form is
  `≤ x^{-δ+ε} · trivial`;
* `QuantitativeTH δ` — the separate **quantitative extension** with explicit `T_H^{7/128}`
  loss, uniform in `T_H ≥ 1`.  The printed statement is *not* assumed to imply it.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-! ### Fixed-local split and modulus bookkeeping -/

/-- `q = f · d` with `(f,d) = 1`. -/
structure FixedLocalSplit (q f d : ℕ) : Prop where
  eq : q = f * d
  coprime : Nat.Coprime f d

theorem fixedLocal_totient {q f d : ℕ} (h : FixedLocalSplit q f d) :
    Nat.totient q = Nat.totient f * Nat.totient d := by
  rw [h.eq, Nat.totient_mul h.coprime]

theorem fixedLocal_bound {q f d F D : ℕ} (h : FixedLocalSplit q f d) (hf : f ≤ F)
    (hd : d ≤ D) : q ≤ F * D := by
  rw [h.eq]; exact Nat.mul_le_mul hf hd

/-! ### CRT phase identity -/

/-- **CRT phase identity (integer form).** -/
theorem crt_phase_split {q1 q2 u v : ℕ} (hq : Nat.Coprime q1 q2) (hu : u * q2 ≡ 1 [MOD q1])
    (hv : v * q1 ≡ 1 [MOD q2]) (a : ℕ) :
    a * u * q2 + a * v * q1 ≡ a [MOD q1 * q2] := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hq]
  constructor
  · have h1 : a * v * q1 ≡ 0 [MOD q1] := Nat.modEq_zero_iff_dvd.2 (Dvd.intro_left _ rfl)
    have h2 : a * u * q2 ≡ a * 1 [MOD q1] := by
      rw [mul_assoc]; exact Nat.ModEq.mul_left a hu
    simpa using h2.add h1
  · have h1 : a * u * q2 ≡ 0 [MOD q2] := Nat.modEq_zero_iff_dvd.2 (Dvd.intro_left _ rfl)
    have h2 : a * v * q1 ≡ a * 1 [MOD q2] := by
      rw [mul_assoc]; exact Nat.ModEq.mul_left a hv
    simpa using h1.add h2

/-- **CRT phase identity (fractional form):** `a u/q₁ + a v/q₂ - a/(q₁q₂) ∈ ℤ`. -/
theorem crt_phase_split_real {q1 q2 u v : ℕ} (h1 : 0 < q1) (h2 : 0 < q2)
    (hq : Nat.Coprime q1 q2) (hu : u * q2 ≡ 1 [MOD q1]) (hv : v * q1 ≡ 1 [MOD q2]) (a : ℕ) :
    ∃ k : ℤ, ((a * u : ℕ) : ℝ) / q1 + ((a * v : ℕ) : ℝ) / q2 = (a : ℝ) / (q1 * q2) + k := by
  have h := (Nat.modEq_iff_dvd.1 (crt_phase_split hq hu hv a).symm)
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h1' : (q1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have h2' : (q2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  have hk' : ((a * u * q2 + a * v * q1 : ℕ) : ℝ) - (a : ℝ) = ((q1 * q2 : ℕ) : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  push_cast at hk' ⊢
  field_simp
  linear_combination hk'

/-! ### Fourier-length enlargement -/

/-- Dual (Poisson) length for modulus `q` and length `N`: `q / N`. -/
def dualLength (q N : ℚ) : ℚ := q / N

/-- **Fourier enlargement by `f`:** the dual length for modulus `fq` is `f` times larger. -/
theorem dualLength_enlarged (f q N : ℚ) : dualLength (f * q) N = f * dualLength q N := by
  unfold dualLength; ring

/-- Regression: forgetting the enlargement is wrong as soon as `f ≠ 1`. -/
theorem forgetting_enlargement_wrong {f q N : ℚ} (hf : f ≠ 1) (hq : q ≠ 0) (hN : N ≠ 0) :
    dualLength (f * q) N ≠ dualLength q N := by
  rw [dualLength_enlarged]
  intro h
  unfold dualLength at h
  have : q / N ≠ 0 := div_ne_zero hq hN
  exact hf (mul_right_cancel₀ this (by rw [one_mul]; exact h))

/-! ### The spectral (Kloosterman-type) bilinear form -/

/-- Modular inverse `r̄ (mod q)` as a natural number in `[0, q)`. -/
def modInv (r q : ℕ) : ℕ := ((r : ZMod q)⁻¹).val

/-- `𝒦 = ∑_{q∈𝒬} ∑_{r∈ℛ, (r,q)=1} ∑_{h∈ℋ} α_q β_r γ_h cos(2π h r̄ / q)`. -/
noncomputable def kloostermanForm (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Qset, ∑ r ∈ Rset.filter (fun r => Nat.Coprime r q), ∑ h ∈ Hset,
    α q * β r * γ h * Real.cos (2 * Real.pi * ((h * modInv r q : ℕ) : ℝ) / q)

/-- Coefficient placement over a decomposition of the modulus set into two disjoint pieces
(e.g. the fixed-local classes). -/
theorem kloostermanForm_split (Q1 Q2 Rset Hset : Finset ℕ) (hdis : Disjoint Q1 Q2)
    (α β γ : ℕ → ℝ) :
    kloostermanForm (Q1 ∪ Q2) Rset Hset α β γ =
      kloostermanForm Q1 Rset Hset α β γ + kloostermanForm Q2 Rset Hset α β γ := by
  unfold kloostermanForm
  rw [Finset.sum_union hdis]

/-- Trivial bound size `∑|α| ∑|β| ∑|γ|`. -/
noncomputable def trivialSize (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) : ℝ :=
  (∑ q ∈ Qset, |α q|) * (∑ r ∈ Rset, |β r|) * (∑ h ∈ Hset, |γ h|)

/-- **All hypotheses of the `E₂` estimate**, as separate fields. -/
structure E2Hypotheses (x : ℝ) (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ)
    (θQ θR θH : ℝ) (TH : ℝ) : Prop where
  coeff_alpha : ∀ q ∈ Qset, |α q| ≤ 1
  coeff_beta : ∀ r ∈ Rset, |β r| ≤ 1
  coeff_gamma : ∀ h ∈ Hset, |γ h| ≤ 1
  Q_range : ∀ q ∈ Qset, 1 ≤ q ∧ (q : ℝ) ≤ x ^ θQ
  R_range : ∀ r ∈ Rset, 1 ≤ r ∧ (r : ℝ) ≤ x ^ θR
  H_range : ∀ h ∈ Hset, (h : ℝ) ≤ x ^ θH
  TH_ge_one : 1 ≤ TH

/-- **Pascadi-type `E₂` estimate, printed shape (external; never constructed).**  For every
fixed small `ε > 0`, with `T_H ≤ x^ε`: `|𝒦| ≤ x^{-δ+ε} · trivial`. -/
def PascadiE2Printed (θQ θR θH δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) (TH : ℝ),
    E2Hypotheses x Qset Rset Hset α β γ θQ θR θH TH → TH ≤ x ^ ε →
      |kloostermanForm Qset Rset Hset α β γ| ≤ x ^ (-δ + ε) * trivialSize Qset Rset Hset α β γ

/-- The V97 quantitative `T_H` loss exponent. -/
def THLossExponent : ℚ := 7 / 128

/-- **Quantitative `T_H` extension (separate external provider; never constructed).**
`|𝒦| ≤ C · T_H^{7/128} · x^{-δ} · trivial`, uniformly in `T_H ≥ 1`. -/
def QuantitativeTH (θQ θR θH δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (Qset Rset Hset : Finset ℕ) (α β γ : ℕ → ℝ) (TH : ℝ),
    E2Hypotheses x Qset Rset Hset α β γ θQ θR θH TH →
      |kloostermanForm Qset Rset Hset α β γ| ≤
        C * TH ^ ((THLossExponent : ℚ) : ℝ) * x ^ (-δ) * trivialSize Qset Rset Hset α β γ

theorem THLossExponent_eq : THLossExponent = 7 / 128 := rfl

end Erdos287.CurrentTail
