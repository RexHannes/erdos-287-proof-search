import Mathlib

/-!
# Erdős #287 — Research Bank V10 §M: the well-factorability cutoff firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Permanent firewall: *well-factorable at level `D`* does **not** imply that multiplying by
`1_{d ≤ D'}` produces a sequence well-factorable at level `D'`.

* `WellFactorable λ D` — for every factorization `R S = D` (over `ℕ`) there are coefficients
  `|α|, |β| ≤ 1`, supported on `[1, R]`, `[1, S]`, with `λ = α ⋆ β`;
* `delta3_wellFactorable_6` — `λ = δ₃` is well-factorable at level `6`;
* `delta3_truncated_not_wellFactorable_4` — `λ · 1_{d ≤ 4} = δ₃` is **not** well-factorable at
  level `4` (the factorization `2·2` cannot produce `3`);
* `wf_truncation_not_automatic` — hence the invalid implication is refuted.

The repaired architecture as a **data-flow theorem** (`truncated_eq_product_cutoff`,
`cutoff_separated_bilinear`):

1. choose a legal factorization `λ = α ⋆ β` at the **original** level;
2. insert the product cutoff `1_{ab ≤ D'}` afterwards (exact identity);
3. separate it by an (external) separation of variables `1_{ab ≤ D'} ≈ ∑_j f_j(a) g_j(b)`; each
   piece `(α f_j) ⋆ (β g_j)` keeps the **original** supports `[1, R] × [1, S]`, with an explicit
   error `≤ ε · #{(a, b) : ab = n}`.

The Mellin/Fourier construction of the separation is external (`MellinSeparationProvider`).
-/

namespace Erdos287
namespace ResearchBankV10
namespace WellFactorableCutoff

open Finset

variable {K : Type*} [CommRing K]

/-- Dirichlet convolution on `ℕ`. -/
def dconv (α β : ℕ → K) (n : ℕ) : K := ∑ x ∈ n.divisorsAntidiagonal, α x.1 * β x.2

/-- Support in `[1, R]`. -/
def SupportedOn (α : ℕ → K) (R : ℕ) : Prop := ∀ n, α n ≠ 0 → 1 ≤ n ∧ n ≤ R

/-- Well-factorability at level `D` (integer model). -/
def WellFactorable (lam : ℕ → ℤ) (D : ℕ) : Prop :=
  ∀ R S : ℕ, R * S = D → ∃ α β : ℕ → ℤ, (∀ n, |α n| ≤ 1) ∧ (∀ n, |β n| ≤ 1) ∧
    SupportedOn α R ∧ SupportedOn β S ∧ ∀ n, lam n = dconv α β n

/-- Truncation `λ · 1_{d ≤ D'}`. -/
def truncate {K : Type*} [Zero K] (lam : ℕ → K) (D' : ℕ) (n : ℕ) : K :=
  if n ≤ D' then lam n else 0

/-- `δ_k`. -/
def delta (k : ℕ) (n : ℕ) : ℤ := if n = k then 1 else 0

theorem dconv_delta_one_left (β : ℕ → ℤ) (n : ℕ) :
    dconv (delta 1) β n = if n = 0 then 0 else β n := by
  unfold dconv
  split_ifs with hn
  · subst hn; simp
  · rw [Finset.sum_eq_single (1, n)]
    · simp [delta]
    · rintro ⟨a, b⟩ hab hne
      have := Nat.mem_divisorsAntidiagonal.1 hab
      simp only [delta]
      split_ifs with ha
      · subst ha; simp at this; exact absurd (by rw [this.1]) hne
      · simp
    · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨by simp, hn⟩) h

theorem dconv_delta_one_right (α : ℕ → ℤ) (n : ℕ) :
    dconv α (delta 1) n = if n = 0 then 0 else α n := by
  unfold dconv
  split_ifs with hn
  · subst hn; simp
  · rw [Finset.sum_eq_single (n, 1)]
    · simp [delta]
    · rintro ⟨a, b⟩ hab hne
      have := Nat.mem_divisorsAntidiagonal.1 hab
      simp only [delta]
      split_ifs with hb
      · subst hb; simp at this; exact absurd (by rw [this.1]) hne
      · simp
    · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨by simp, hn⟩) h

theorem abs_delta_le (k n : ℕ) : |delta k n| ≤ 1 := by
  unfold delta; split_ifs <;> simp

theorem delta_supported {k R : ℕ} (hk : 1 ≤ k) (hkR : k ≤ R) : SupportedOn (delta k) R := by
  intro n hn
  unfold delta at hn
  split_ifs at hn with h
  · subst h; exact ⟨hk, hkR⟩
  · exact absurd rfl hn

/-- **`δ₃` is well-factorable at level `6`.** -/
theorem delta3_wellFactorable_6 : WellFactorable (delta 3) 6 := by
  intro R S hRS
  have hS1 : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h; simp at hRS
    · exact h
  have hR1 : 1 ≤ R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · subst h; simp at hRS
    · exact h
  by_cases hR : 3 ≤ R
  · refine ⟨delta 3, delta 1, abs_delta_le 3, abs_delta_le 1, delta_supported (by norm_num) hR,
      delta_supported le_rfl hS1, fun n => ?_⟩
    rw [dconv_delta_one_right]
    split_ifs with hn
    · subst hn; simp [delta]
    · rfl
  · have hS : 3 ≤ S := by
      interval_cases R <;> omega
    refine ⟨delta 1, delta 3, abs_delta_le 1, abs_delta_le 3, delta_supported le_rfl hR1,
      delta_supported (by norm_num) hS, fun n => ?_⟩
    rw [dconv_delta_one_left]
    split_ifs with hn
    · subst hn; simp [delta]
    · rfl

/-- **`δ₃ · 1_{d ≤ 4}` is not well-factorable at level `4`.** -/
theorem delta3_truncated_not_wellFactorable_4 : ¬ WellFactorable (truncate (delta 3) 4) 4 := by
  intro h
  obtain ⟨α, β, -, -, hα, hβ, hconv⟩ := h 2 2 rfl
  have h3 := hconv 3
  have hanti : (3 : ℕ).divisorsAntidiagonal = {(1, 3), (3, 1)} := by decide
  rw [dconv, hanti, Finset.sum_pair (by decide)] at h3
  have hβ3 : β 3 = 0 := by
    by_contra hne; have := (hβ 3 hne).2; omega
  have hα3 : α 3 = 0 := by
    by_contra hne; have := (hα 3 hne).2; omega
  simp [truncate, delta, hβ3, hα3] at h3

/-- **Firewall**: level-`D` well-factorability does not imply truncated well-factorability at a
smaller level `D'`. -/
theorem wf_truncation_not_automatic :
    ¬ ∀ (lam : ℕ → ℤ) (D D' : ℕ), D' ≤ D → WellFactorable lam D →
      WellFactorable (truncate lam D') D' :=
  fun h => delta3_truncated_not_wellFactorable_4 (h _ 6 4 (by norm_num) delta3_wellFactorable_6)

/-! ## The repaired data flow -/

/-- **Step 2 (exact)**: after a legal factorization `λ = α ⋆ β`, the truncation is the bilinear
sum with the product cutoff inserted termwise. -/
theorem truncated_eq_product_cutoff (lam α β : ℕ → K) (hconv : ∀ n, lam n = dconv α β n)
    (D' n : ℕ) :
    truncate lam D' n =
      ∑ x ∈ n.divisorsAntidiagonal, α x.1 * β x.2 * (if x.1 * x.2 ≤ D' then 1 else 0) := by
  unfold truncate
  rw [hconv, dconv]
  split_ifs with hn
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.1 hx).1, if_pos hn, mul_one]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.1 hx).1, if_neg hn, mul_zero]

/-- A separation of the product cutoff into finitely many bilinear pieces with uniform error
`ε` on `a, b ≥ 1` (the object produced by a Mellin/Fourier argument). -/
structure CutoffSeparation (D' : ℕ) (ε : ℝ) where
  J : Finset ℕ
  f : ℕ → ℕ → ℂ
  g : ℕ → ℕ → ℂ
  err : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ‖((if a * b ≤ D' then 1 else 0 : ℂ)) - ∑ j ∈ J, f j a * g j b‖ ≤ ε

/-- **External**: the Mellin/Fourier separation of the cutoff exists (never inhabited here). -/
structure MellinSeparationProvider (D' : ℕ) (ε : ℝ) : Prop where
  exists_sep : Nonempty (CutoffSeparation D' ε)

/-- Each separated piece keeps the original supports. -/
theorem piece_supported {α : ℕ → ℂ} {R : ℕ} (hα : SupportedOn α R) (f : ℕ → ℂ) :
    SupportedOn (fun a => α a * f a) R := by
  intro n hn
  exact hα n (left_ne_zero_of_mul hn)

/-- **Step 3 (data-flow theorem)**: legal factorization first, cutoff inserted afterwards, then
separated: the truncation equals the sum of the bilinear pieces `(α f_j) ⋆ (β g_j)` (each with the
original supports) up to `ε · #{(a, b) : ab = n}`. -/
theorem cutoff_separated_bilinear (lam α β : ℕ → ℂ) (hconv : ∀ n, lam n = dconv α β n)
    (hα : ∀ n, ‖α n‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1) {D' : ℕ} {ε : ℝ}
    (sep : CutoffSeparation D' ε) (n : ℕ) :
    ‖truncate lam D' n -
        ∑ j ∈ sep.J, dconv (fun a => α a * sep.f j a) (fun b => β b * sep.g j b) n‖ ≤
      ε * (n.divisorsAntidiagonal.card : ℝ) := by
  rw [truncated_eq_product_cutoff lam α β hconv]
  have hsum : ∑ j ∈ sep.J, dconv (fun a => α a * sep.f j a) (fun b => β b * sep.g j b) n =
      ∑ x ∈ n.divisorsAntidiagonal, α x.1 * β x.2 * ∑ j ∈ sep.J, sep.f j x.1 * sep.g j x.2 := by
    unfold dconv
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, ← Finset.sum_sub_distrib]
  calc ‖∑ x ∈ n.divisorsAntidiagonal, (α x.1 * β x.2 * (if x.1 * x.2 ≤ D' then 1 else 0) -
          α x.1 * β x.2 * ∑ j ∈ sep.J, sep.f j x.1 * sep.g j x.2)‖
      ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖α x.1 * β x.2 * (if x.1 * x.2 ≤ D' then 1 else 0) -
          α x.1 * β x.2 * ∑ j ∈ sep.J, sep.f j x.1 * sep.g j x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal, ε := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hmem := Nat.mem_divisorsAntidiagonal.1 hx
        have ha : 1 ≤ x.1 := Nat.pos_of_ne_zero fun h => hmem.2 (by rw [← hmem.1, h, zero_mul])
        have hb : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h => hmem.2 (by rw [← hmem.1, h, mul_zero])
        rw [← mul_sub, norm_mul, norm_mul]
        have h1 := hα x.1
        have h2 := hβ x.2
        have h3 := sep.err x.1 x.2 ha hb
        have h0 : 0 ≤ ‖((if x.1 * x.2 ≤ D' then 1 else 0 : ℂ)) -
            ∑ j ∈ sep.J, sep.f j x.1 * sep.g j x.2‖ := norm_nonneg _
        calc ‖α x.1‖ * ‖β x.2‖ * ‖((if x.1 * x.2 ≤ D' then 1 else 0 : ℂ)) -
              ∑ j ∈ sep.J, sep.f j x.1 * sep.g j x.2‖
            ≤ 1 * 1 * ε := by gcongr
          _ = ε := by ring
    _ = ε * (n.divisorsAntidiagonal.card : ℝ) := by simp [mul_comm]

end WellFactorableCutoff
end ResearchBankV10
end Erdos287
