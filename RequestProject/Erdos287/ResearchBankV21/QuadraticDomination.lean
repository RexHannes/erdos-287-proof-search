import RequestProject.Erdos287.ResearchBankV21.NormalizedSieveMonotonicity
import RequestProject.Erdos287.ResearchBankV21.ConditionalDensity

/-!
# Erdős #287 — Research Bank V21 §5: spectator-conditioned quadratic domination

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The finite principal model.  Spectator states `y` range over a finite type `Ys` with a
nonnegative law `μ`.  Conditionally on `y`, the divisibility pattern `D ⊆ P` of `L_j` by the
sieve primes has the product law with densities `qY y p` (independence of the finite CRT
coordinates **in the principal model only** — nothing is claimed about actual primes):

    patternProb q D = ∏_{p∈D} q_p ∏_{p∉D} (1 - q_p).

The sieve value is `S_λ(L_j) = a_λ(D)`, and `L_j` is sifted iff `D = ∅`.

Kernel-proved (LEAN BANK):
* `patternProb_sum` — the conditional law has mass one;
* `condExp_sieve` — `E[S_λ(L_j) | y] = ∑_A λ(A) ∏_{p∈A} q_p(y)`;
* `condProb_sifted` — `Prob(L_j sifted | y) = ∏_p (1 - q_p(y))`;
* `condExp_eq_normCost_mul` — `E[S_λ | y] = C_λ(q(y)) · Prob(sifted | y)`;
* `condExp_le_envelope` — `E[S_λ | y] ≤ C_λ(h) · Prob(sifted | y)` if `q(y) ≤ h < 1`;
* **`quadratic_domination`** — for an ARBITRARY complex amplitude `B : Ys → ℂ`
  (measurable w.r.t. the spectator states, any signs inside `B` before squaring),

      E[ |B|² S_λ(L_j) ] ≤ C_λ(h) · E[ |B|² 1_sifted ];

* `quadratic_domination_signed_tensor` — the same with `B = ∑_e c_e φ_e` a signed tensor;
* `quadratic_domination_spectator` — the product spectator model of §3 over all sieve primes
  (every spectator state retained, envelope `h(p) = 1/(p-r-1)`).
-/

namespace Erdos287
namespace ResearchBankV21
namespace QuadraticDomination

open Finset FiniteSieveSetup NormalizedSieveMonotonicity SpectatorStates

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The conditional product law of the divisibility pattern `D`. -/
def patternProb (q : P → ℝ) (D : Finset P) : ℝ := (∏ p ∈ D, q p) * ∏ p ∈ Dᶜ, (1 - q p)

theorem patternProb_nonneg {q : P → ℝ} (hq0 : ∀ p, 0 ≤ q p) (hq1 : ∀ p, q p ≤ 1)
    (D : Finset P) : 0 ≤ patternProb q D :=
  mul_nonneg (prod_nonneg fun p _ => hq0 p) (prod_nonneg fun p _ => by linarith [hq1 p])

theorem patternProb_sum (q : P → ℝ) : ∑ D : Finset P, patternProb q D = 1 := by
  have := sum_supset_prod (∅ : Finset P) q (fun p => 1 - q p)
  simp only [empty_subset, if_true, prod_empty, one_mul, add_sub_cancel, prod_const_one] at this
  exact this

/-- `E[S_λ(L_j) | y] = ∑_A λ(A) ∏_{p∈A} q_p`. -/
theorem condExp_sieve (lam : Finset P → ℝ) (q : P → ℝ) :
    ∑ D : Finset P, patternProb q D * divSum lam D = numer lam q := by
  simp_rw [mul_comm (patternProb q _)]
  rw [sum_divSum_mul]
  unfold numer
  refine sum_congr rfl fun A _ => ?_
  congr 1
  have := sum_supset_prod A q (fun p => 1 - q p)
  simp only [add_sub_cancel, prod_const_one, mul_one] at this
  rw [← this]
  rfl

/-- `Prob(L_j sifted | y) = ∏_p (1 - q_p)`. -/
theorem condProb_sifted (q : P → ℝ) :
    ∑ D : Finset P, patternProb q D * (if D = ∅ then 1 else 0) = denom q := by
  rw [sum_eq_single (∅ : Finset P)]
  · simp [patternProb, denom]
  · intro D _ hD; simp [hD]
  · simp

/-- `E[S_λ | y] = C_λ(q(y)) · Prob(sifted | y)`. -/
theorem condExp_eq_normCost_mul (lam : Finset P → ℝ) (q : P → ℝ) (hq : ∀ p, q p < 1) :
    ∑ D : Finset P, patternProb q D * divSum lam D =
      normCost lam q * ∑ D : Finset P, patternProb q D * (if D = ∅ then 1 else 0) := by
  rw [condExp_sieve, condProb_sifted]
  have : denom q ≠ 0 := prod_ne_zero_iff.2 fun p _ => by linarith [hq p]
  unfold normCost
  field_simp

theorem condProb_sifted_nonneg {q : P → ℝ} (hq : ∀ p, q p < 1) :
    0 ≤ ∑ D : Finset P, patternProb q D * (if D = ∅ then 1 else 0) := by
  rw [condProb_sifted]
  exact prod_nonneg fun p _ => by linarith [hq p]

/-- **Conditional envelope bound** `E[S_λ | y] ≤ C_λ(h) · Prob(sifted | y)`. -/
theorem condExp_le_envelope (lam : Finset P → ℝ) (hdiv : ∀ S, 0 ≤ divSum lam S) {q h : P → ℝ}
    (hq0 : ∀ p, 0 ≤ q p) (hqh : ∀ p, q p ≤ h p) (hh : ∀ p, h p < 1) :
    ∑ D : Finset P, patternProb q D * divSum lam D ≤
      normCost lam h * ∑ D : Finset P, patternProb q D * (if D = ∅ then 1 else 0) := by
  have hq1 : ∀ p, q p < 1 := fun p => lt_of_le_of_lt (hqh p) (hh p)
  rw [condExp_eq_normCost_mul lam q hq1]
  exact mul_le_mul_of_nonneg_right (normCost_mono lam hdiv hq0 hqh hh)
    (condProb_sifted_nonneg hq1)

variable {Ys : Type*} [Fintype Ys]

/-- Expectation in the joint finite principal model: `y ∼ μ`, then `D ∼ patternProb (qY y)`. -/
def jointExp (μ : Ys → ℝ) (qY : Ys → P → ℝ) (F : Ys → Finset P → ℝ) : ℝ :=
  ∑ y, ∑ D : Finset P, μ y * patternProb (qY y) D * F y D

/-- **Spectator-conditioned quadratic domination.**  For every complex amplitude `B` depending
on the spectator states only (arbitrary signs inside `B`, squared afterwards),

    E[ |B|² S_λ(L_j) ] ≤ C_λ(h) · E[ |B|² 1_{L_j sifted} ].

Hypotheses: `μ ≥ 0`, `0 ≤ q_p(y) ≤ h_p < 1`, and nonnegative DIVISOR SUMS `a_λ ≥ 0` (the
coefficients `λ` themselves may be signed). -/
theorem quadratic_domination (lam : Finset P → ℝ) (hdiv : ∀ S, 0 ≤ divSum lam S)
    (μ : Ys → ℝ) (hμ : ∀ y, 0 ≤ μ y) (qY : Ys → P → ℝ) (h : P → ℝ)
    (hq0 : ∀ y p, 0 ≤ qY y p) (hqh : ∀ y p, qY y p ≤ h p) (hh : ∀ p, h p < 1) (B : Ys → ℂ) :
    jointExp μ qY (fun y D => ‖B y‖ ^ 2 * divSum lam D) ≤
      normCost lam h * jointExp μ qY (fun y D => ‖B y‖ ^ 2 * (if D = ∅ then 1 else 0)) := by
  unfold jointExp
  rw [mul_sum]
  refine sum_le_sum fun y _ => ?_
  have e1 : ∑ D : Finset P, μ y * patternProb (qY y) D * (‖B y‖ ^ 2 * divSum lam D) =
      (μ y * ‖B y‖ ^ 2) * ∑ D : Finset P, patternProb (qY y) D * divSum lam D := by
    rw [mul_sum]; exact sum_congr rfl fun D _ => by ring
  have e2 : normCost lam h * ∑ D : Finset P, μ y * patternProb (qY y) D *
      (‖B y‖ ^ 2 * (if D = ∅ then 1 else 0)) = (μ y * ‖B y‖ ^ 2) * (normCost lam h *
      ∑ D : Finset P, patternProb (qY y) D * (if D = ∅ then 1 else 0)) := by
    rw [mul_sum, mul_sum, mul_sum]; exact sum_congr rfl fun D _ => by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (condExp_le_envelope lam hdiv (hq0 y) (hqh y) hh)
    (mul_nonneg (hμ y) (sq_nonneg _))

/-- **Signed tensor form**: `B = ∑_e c_e φ_e` with arbitrary complex (signed) coefficients;
signs recombine inside `|B|²` before the domination is applied. -/
theorem quadratic_domination_signed_tensor {ι : Type*} [Fintype ι] (lam : Finset P → ℝ)
    (hdiv : ∀ S, 0 ≤ divSum lam S) (μ : Ys → ℝ) (hμ : ∀ y, 0 ≤ μ y) (qY : Ys → P → ℝ)
    (h : P → ℝ) (hq0 : ∀ y p, 0 ≤ qY y p) (hqh : ∀ y p, qY y p ≤ h p) (hh : ∀ p, h p < 1)
    (c : ι → ℂ) (φ : ι → Ys → ℂ) :
    jointExp μ qY (fun y D => ‖∑ e, c e * φ e y‖ ^ 2 * divSum lam D) ≤
      normCost lam h *
        jointExp μ qY (fun y D => ‖∑ e, c e * φ e y‖ ^ 2 * (if D = ∅ then 1 else 0)) :=
  quadratic_domination lam hdiv μ hμ qY h hq0 hqh hh (fun y => ∑ e, c e * φ e y)

/-- The product spectator law over all sieve primes (`pv p` is the prime attached to `p`). -/
noncomputable def spectatorLaw (pv : P → ℕ) (r : ℕ) (y : P → SpecState r) : ℝ :=
  ∏ p, stateProb (pv p) r (y p)

omit [DecidableEq P] in
theorem spectatorLaw_nonneg {pv : P → ℕ} {r : ℕ} (hp : ∀ p, r + 1 < pv p)
    (y : P → SpecState r) : 0 ≤ spectatorLaw pv r y :=
  prod_nonneg fun p _ => stateProb_nonneg (hp p) (y p)

/-- **Quadratic domination in the product spectator model** (all spectator states retained):
`q_p(y) = condDensity (y p)` and the envelope is `h(p) = 1/(p-r-1)`. -/
theorem quadratic_domination_spectator (lam : Finset P → ℝ) (hdiv : ∀ S, 0 ≤ divSum lam S)
    (pv : P → ℕ) (r : ℕ) (hp : ∀ p, r + 2 < pv p) (B : (P → SpecState r) → ℂ) :
    jointExp (spectatorLaw pv r) (fun y p => condDensity (pv p) r (y p))
        (fun y D => ‖B y‖ ^ 2 * divSum lam D) ≤
      normCost lam (fun p => envelope (pv p) r) *
        jointExp (spectatorLaw pv r) (fun y p => condDensity (pv p) r (y p))
          (fun y D => ‖B y‖ ^ 2 * (if D = ∅ then 1 else 0)) :=
  have hp1 : ∀ p, r + 1 < pv p := fun p => by have := hp p; omega
  quadratic_domination (μ := spectatorLaw pv r) (qY := fun y p => condDensity (pv p) r (y p))
    (h := fun p => envelope (pv p) r) lam hdiv (spectatorLaw_nonneg hp1)
    (fun y p => condDensity_nonneg (hp1 p) (y p))
    (fun y p => condDensity_le_envelope (hp1 p) (y p))
    (fun p => envelope_lt_one (hp p)) B

end QuadraticDomination
end ResearchBankV21
end Erdos287
