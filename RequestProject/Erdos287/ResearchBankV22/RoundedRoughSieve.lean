import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V22 §3: the rounded rough sieve (definitions)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Squarefree moduli `d = p₁ ⋯ p_k` are represented by the finite sets `A = {p₁, …, p_k}` of their
prime atoms (over any linearly ordered atom type `γ`; for actual primes `γ = ℕ`).  A weight is a
function `Finset γ → ℝ`.

* `dsum w D = ∑_{A ⊆ D} w A` — the divisor sum `S_w(n)` of a squarefree-supported weight at an
  integer `n` whose set of relevant prime divisors is `D`;
* `SupportedIn w U` — every modulus in the support of `w` has all its atoms in `U`;
* `above A p = {q ∈ A : p < q}` — for `A` ordered decreasingly `p₁ > ⋯ > p_k`, the atoms before
  `p = p_j` are `above A p = {p₁,…,p_{j-1}}`, so `j = |above A p| + 1` and **`j` is odd iff
  `|above A p|` is even**;
* `Adm cond A` — for every odd index `j`, `cond {p₁,…,p_{j-1}} p_j` holds;
* `ellW cond A = μ(A) · 1_{Adm cond A} = (-1)^{|A|} 1_{Adm cond A}`;
* `roundedCond w X B p := (∏_{q∈B} w q) · w(p)³ ≤ X` — the rounded rough condition
  `w(p₁)⋯w(p_{j-1}) w(p_j)³ ≤ x^{vartheta0}` with `X = x^{vartheta0}`;
* `ellRd U w X` — the rounded rough sieve weight `ℓ_rd`, supported on the rough universe `U`;
* `RoundingData U τ w` — cell upper endpoints: `p ≤ w(p) ≤ p^{1+τ}`, monotone in `p`.

Kernel-proved: `dsum_inter` (support restriction), `ellW_empty`.
-/

namespace Erdos287
namespace ResearchBankV22
namespace RoundedRoughSieve

open Finset

section Generic

variable {γ : Type*} [DecidableEq γ]

/-- Divisor sum of a squarefree-supported weight: `S_w(D) = ∑_{A ⊆ D} w A`. -/
def dsum (w : Finset γ → ℝ) (D : Finset γ) : ℝ := ∑ A ∈ D.powerset, w A

/-- Support of a weight inside an atom universe `U`. -/
def SupportedIn (w : Finset γ → ℝ) (U : Finset γ) : Prop := ∀ A, w A ≠ 0 → A ⊆ U

/-- One-boundedness `|w| ≤ 1`. -/
def OneBounded (w : Finset γ → ℝ) : Prop := ∀ A, |w A| ≤ 1

/-- **Support restriction**: a weight supported in `U` only sees `D ∩ U`. -/
theorem dsum_inter {w : Finset γ → ℝ} {U : Finset γ} (hw : SupportedIn w U) (D : Finset γ) :
    dsum w D = dsum w (D ∩ U) := by
  unfold dsum
  symm
  refine sum_subset (powerset_mono.2 inter_subset_left) fun A hA hA' => ?_
  by_contra hne
  have h1 := hw A hne
  exact hA' (mem_powerset.2 (subset_inter (mem_powerset.1 hA) h1))

end Generic

section Ordered

variable {γ : Type*} [LinearOrder γ]

/-- The atoms of `A` above `p`: for `A = {p₁ > ⋯ > p_k}` and `p = p_j`, `{p₁,…,p_{j-1}}`. -/
def above (A : Finset γ) (p : γ) : Finset γ := A.filter (p < ·)

/-- Admissibility: at every ODD index `j` (`|above A p_j|` even) the condition holds. -/
def Adm (cond : Finset γ → γ → Prop) (A : Finset γ) : Prop :=
  ∀ p ∈ A, Even (above A p).card → cond (above A p) p

open Classical in
/-- `ℓ(A) = μ(A) · 1_{Adm cond A}`. -/
noncomputable def ellW (cond : Finset γ → γ → Prop) (A : Finset γ) : ℝ :=
  if Adm cond A then (-1 : ℝ) ^ A.card else 0

theorem adm_empty (cond : Finset γ → γ → Prop) : Adm cond ∅ := fun p hp => absurd hp (by simp)

theorem ellW_empty (cond : Finset γ → γ → Prop) : ellW cond ∅ = 1 := by
  simp [ellW, adm_empty]

theorem ellW_abs_le (cond : Finset γ → γ → Prop) (A : Finset γ) : |ellW cond A| ≤ 1 := by
  unfold ellW; split_ifs <;> simp

/-- The rounded rough condition `(∏_{q∈B} w q) · w(p)³ ≤ X`. -/
def roundedCond (w : γ → ℝ) (X : ℝ) (B : Finset γ) (p : γ) : Prop :=
  (∏ q ∈ B, w q) * w p ^ 3 ≤ X

open Classical in
/-- **The rounded rough sieve weight** `ℓ_rd`, supported on the rough universe `U`:
`ℓ_rd(d) = μ(d) · 1(∀ odd j, w(p₁)⋯w(p_{j-1}) w(p_j)³ ≤ X)`. -/
noncomputable def ellRd (U : Finset γ) (w : γ → ℝ) (X : ℝ) (A : Finset γ) : ℝ :=
  if A ⊆ U then ellW (roundedCond w X) A else 0

theorem ellRd_supported (U : Finset γ) (w : γ → ℝ) (X : ℝ) : SupportedIn (ellRd U w X) U := by
  intro A hA
  by_contra h
  exact hA (by simp [ellRd, h])

theorem ellRd_oneBounded (U : Finset γ) (w : γ → ℝ) (X : ℝ) : OneBounded (ellRd U w X) := by
  intro A; unfold ellRd; split_ifs
  · exact ellW_abs_le _ _
  · simp

end Ordered

/-- Cell rounding data on the rough universe `U ⊆ ℕ`: `p ≤ w(p) ≤ p^{1+τ}`, monotone. -/
structure RoundingData (U : Finset ℕ) (τ : ℝ) (w : ℕ → ℝ) : Prop where
  lower : ∀ p ∈ U, (p : ℝ) ≤ w p
  upper : ∀ p ∈ U, w p ≤ (p : ℝ) ^ (1 + τ)
  mono : ∀ p ∈ U, ∀ q ∈ U, p ≤ q → w p ≤ w q

/-- The trivial rounding `w(p) = p` is admissible for every `τ ≥ 0`. -/
theorem roundingData_id (U : Finset ℕ) (hU : ∀ p ∈ U, 1 ≤ p) {τ : ℝ} (hτ : 0 ≤ τ) :
    RoundingData U τ (fun p => (p : ℝ)) where
  lower _ _ := le_rfl
  upper p hp := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hU p hp
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ (1 + τ) := Real.rpow_le_rpow_of_exponent_le this (by linarith)
  mono _ _ _ _ h := by exact_mod_cast h

end RoundedRoughSieve
end ResearchBankV22
end Erdos287
