import RequestProject.Erdos287.ResearchBankV21.QuadraticDomination
import RequestProject.Erdos287.ResearchBankV22.RosserCostProvider
import RequestProject.Erdos287.ResearchBankV23.FullLCMPrincipal

/-!
# Erdős #287 — Research Bank V23 §5: the same-weight signed principal functional

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The finite principal model is the V21 product model over the sieve-prime coordinates
(spectator / root-collision states `y ∈ Ys`, divisibility pattern `D` of `L_j`).  For the
completed weight `Λ` (atom-set weight on the universe `U`),

    M_new = Li / (φ(A_i W0) · N) · E[ |B|² S_Λ(L_j) ],
    principalSifted = Li / (φ(A_i W0) · N) · E[ |B|² 1(L_j sifted) ].

Kernel-proved (LEAN BANK):
* **`signed_expansion`** — `E[|B|² S_λ(L_j)]` with `B = Σ_e c_e φ_e` expands EXACTLY to the
  original signed expression `Σ_d λ(d) Σ_{e,e'} c_e \bar c_{e'} E[φ_e \bar φ_{e'} 1_{d|L_j}]`
  (tensor signs before squaring, every spectator state, the same `λ`);
* **`same_weight_principal_bound`** — after the signs have recombined inside `|B|²`,

      M_new ≤ C_Λ(h) · principalSifted,

  with `C_Λ(h) = costU U Λ h` the normalized cost of the SAME weight (V21 quadratic domination);
* **`same_weight_principal_bound_LambdaNewPlus`** — the same for the concrete `Λ_new^+` of V22
  (its divisor sums are nonnegative, so no sign condition on its coefficients is needed);
* `principal_normalizer_fullLCM` — the prefactor `Li/φ(A_i W0)` against the principal CRT
  probability equals `Li/φ(A_i L0)` times the unit indicator at the complete modulus `L0`.
-/

namespace Erdos287
namespace ResearchBankV23
namespace SameWeightPrincipal

open Finset
open ResearchBankV21.FiniteSieveSetup ResearchBankV21.QuadraticDomination
open ResearchBankV22.RoundedRoughSieve ResearchBankV22.CompletedPositiveWeight
open ResearchBankV22.RosserCostProvider

/-- Moving a block of two finite sums past a third. -/
theorem sum_comm_block {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
/-- **Signed expansion** of the principal functional: the positive square `|B|²` of the signed
tensor `B = Σ_e c_e φ_e`, weighted by `S_λ(L_j)`, equals the ORIGINAL signed expression
`Σ_d λ(d) Σ_{e,e'} c_e \bar c_{e'} E[φ_e \bar φ_{e'} 1_{d ∣ L_j}]` — tensor signs, all spectator
(root-collision) states and the same weight `λ` retained. -/
theorem signed_expansion {P Ys ι : Type*} [Fintype P] [DecidableEq P] [Fintype Ys] [Fintype ι]
    (lam : Finset P → ℝ) (μ : Ys → ℝ) (qY : Ys → P → ℝ) (c : ι → ℂ) (φ : ι → Ys → ℂ) :
    ((jointExp μ qY (fun y D => ‖∑ e, c e * φ e y‖ ^ 2 * divSum lam D) : ℝ) : ℂ) =
      ∑ A : Finset P, (lam A : ℂ) * ∑ e, ∑ e', c e * starRingEnd ℂ (c e') *
        ∑ y, ∑ D : Finset P, ((μ y * patternProb (qY y) D : ℝ) : ℂ) *
          (if A ⊆ D then φ e y * starRingEnd ℂ (φ e' y) else 0) := by
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    intro z; rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  have hdiv : ∀ D : Finset P, ((divSum lam D : ℝ) : ℂ) =
      ∑ A : Finset P, if A ⊆ D then (lam A : ℂ) else 0 := by
    intro D; unfold divSum; push_cast; rw [← Finset.sum_filter]; congr 1; ext A; simp
  have hpt : ∀ y (D : Finset P),
      ((μ y * patternProb (qY y) D * (‖∑ e, c e * φ e y‖ ^ 2 * divSum lam D) : ℝ) : ℂ) =
      ∑ A : Finset P, ∑ e, ∑ e', (lam A : ℂ) * (c e * starRingEnd ℂ (c e')) *
        (((μ y * patternProb (qY y) D : ℝ) : ℂ) *
          (if A ⊆ D then φ e y * starRingEnd ℂ (φ e' y) else 0)) := by
    intro y D
    simp only [Complex.ofReal_mul]
    rw [hdiv, Complex.ofReal_pow, hsq, map_sum,
      Finset.sum_mul_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun A _ => sum_congr rfl fun e _ => sum_congr rfl fun e' _ => ?_
    split_ifs <;> simp [map_mul]; ring
  unfold jointExp
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum, hpt]
  simp only [Finset.mul_sum]
  rw [sum_comm_block]
  refine sum_congr rfl fun A _ => ?_
  rw [sum_comm_block]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_comm_block]
  refine sum_congr rfl fun e' _ => sum_congr rfl fun y _ => sum_congr rfl fun D _ => ?_
  ring


section Principal

variable {Ys : Type*} [Fintype Ys] (U : Finset ℕ)

/-- `M_new = Li/(φ N) · E[|B|² S_Λ(L_j)]` in the finite principal model. -/
noncomputable def Mnew (pref : ℝ) (Λ : Finset ℕ → ℝ) (μ : Ys → ℝ) (qY : Ys → U → ℝ)
    (B : Ys → ℂ) : ℝ :=
  pref * jointExp μ qY (fun y D => ‖B y‖ ^ 2 * divSum (pull U Λ) D)

/-- `principalSifted = Li/(φ N) · E[|B|² 1(L_j sifted)]`. -/
noncomputable def principalSifted (pref : ℝ) (μ : Ys → ℝ) (qY : Ys → U → ℝ) (B : Ys → ℂ) : ℝ :=
  pref * jointExp μ qY (fun y D => ‖B y‖ ^ 2 * (if D = ∅ then 1 else 0))

variable {U}

/-- **Same-weight signed-principal bound** `M_new ≤ C_Λ(h) · principalSifted`. -/
theorem same_weight_principal_bound {pref : ℝ} (hpref : 0 ≤ pref) {Λ : Finset ℕ → ℝ}
    (hΛ : ∀ D, 0 ≤ dsum Λ D) {μ : Ys → ℝ} (hμ : ∀ y, 0 ≤ μ y) {qY : Ys → U → ℝ}
    {h : ℕ → ℝ} (hq0 : ∀ y p, 0 ≤ qY y p) (hqh : ∀ y p, qY y p ≤ h p) (hh : ∀ p ∈ U, h p < 1)
    (B : Ys → ℂ) :
    Mnew U pref Λ μ qY B ≤ costU U Λ h * principalSifted U pref μ qY B := by
  unfold Mnew principalSifted
  have hdom := quadratic_domination (pull U Λ) (fun S => by rw [divSum_pull]; exact hΛ _) μ hμ qY
    (fun p : U => h p) hq0 hqh (fun p => hh p p.2) B
  rw [← costU_eq_normCost] at hdom
  calc pref * jointExp μ qY (fun y D => ‖B y‖ ^ 2 * divSum (pull U Λ) D)
      ≤ pref * (costU U Λ h * jointExp μ qY (fun y D => ‖B y‖ ^ 2 * (if D = ∅ then 1 else 0))) :=
        mul_le_mul_of_nonneg_left hdom hpref
    _ = _ := by ring

/-- **The bound for the concrete completed weight `Λ_new^+`.** -/
theorem same_weight_principal_bound_LambdaNewPlus {E Psm Prd : Finset ℕ} {level X : ℝ}
    {w : ℕ → ℝ} (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd)
    {pref : ℝ} (hpref : 0 ≤ pref) {μ : Ys → ℝ} (hμ : ∀ y, 0 ≤ μ y)
    {qY : Ys → (E ∪ Psm ∪ Prd : Finset ℕ) → ℝ} {h : ℕ → ℝ} (hq0 : ∀ y p, 0 ≤ qY y p)
    (hqh : ∀ y p, qY y p ≤ h p) (hh : ∀ p ∈ E ∪ Psm ∪ Prd, h p < 1) (B : Ys → ℂ) :
    Mnew (E ∪ Psm ∪ Prd) pref (LambdaNewPlus E Psm Prd level w X) μ qY B ≤
      costU (E ∪ Psm ∪ Prd) (LambdaNewPlus E Psm Prd level w X) h *
        principalSifted (E ∪ Psm ∪ Prd) pref μ qY B :=
  same_weight_principal_bound hpref (LambdaNewPlus_nonneg h1 h2 h3) hμ hq0 hqh hh B

theorem principalSifted_nonneg {pref : ℝ} (hpref : 0 ≤ pref) {μ : Ys → ℝ} (hμ : ∀ y, 0 ≤ μ y)
    {qY : Ys → U → ℝ} (hq0 : ∀ y p, 0 ≤ qY y p) (hq1 : ∀ y p, qY y p ≤ 1) (B : Ys → ℂ) :
    0 ≤ principalSifted U pref μ qY B := by
  unfold principalSifted jointExp
  refine mul_nonneg hpref (sum_nonneg fun y _ => sum_nonneg fun D _ => ?_)
  refine mul_nonneg (mul_nonneg (hμ y) (patternProb_nonneg (hq0 y) (hq1 y) D)) ?_
  exact mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)

end Principal

/-- **Principal normalizer at the complete modulus**: the prefactor `Li/φ(A W0)` against the
exact principal CRT probability is `Li/φ(A L0)` times the unit indicator,
`L0 = lcm(W0, s, q₁, …, q_r)`. -/
theorem principal_normalizer_fullLCM {A W0 s tW : ℕ} {qs : List ℕ} (hA : 0 < A) (hW : 0 < W0)
    (hs : 0 < s) (hq : ∀ q ∈ qs, 0 < q) (hc : Nat.Coprime (A * tW + 1) (A * W0)) (Li : ℝ)
    (F : ℕ → ℝ) :
    Li / Nat.totient (A * W0) *
        ∑ t0 ∈ (range (FullLCMPrincipal.fullLCM W0 s qs)).filter (· ≡ tW [MOD W0]),
          PrincipalCRTMeasure.principalProb A W0 (FullLCMPrincipal.fullLCM W0 s qs) tW t0 * F t0 =
      Li / Nat.totient (A * FullLCMPrincipal.fullLCM W0 s qs) *
        ∑ t0 ∈ (range (FullLCMPrincipal.fullLCM W0 s qs)).filter (· ≡ tW [MOD W0]),
          (if Nat.gcd (A * t0 + 1) (A * FullLCMPrincipal.fullLCM W0 s qs) = 1 then 1 else 0) *
            F t0 :=
  FullLCMPrincipal.principal_sum_fullLCM hA hW hs hq hc Li F

end SameWeightPrincipal
end ResearchBankV23
end Erdos287
