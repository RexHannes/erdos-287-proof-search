import RequestProject.Erdos287.SourceChain.OAIImport.Defs
import RequestProject.Erdos287.CurrentTail.ExactSource

/-!
# Erdős #287 — source chain: exact dictionary between the external BV/SW statements and the
project's progression notation

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Kernel-proved, with no analytic content:

* `progSum_vonMangoldt_eq_residuePrefix` — the project's `progSum (Ioc 0 N) Λ q a` is the
  external `residuePrefix Λ N q (a % q)`;
* `abs_progErr_le_endpointError` — for `(a, q) = 1`, `|progErr (Ioc 0 ⌊x⌋) Λ x q a|` is bounded
  by the external `endpointError x q`;
* `psiBVProjectForm_of_OAI` — the external BV statement, rewritten in project notation with an
  arbitrary choice of reduced residues `r(q)` (the maximal form);
* `tinyModulusSW_of_OAIBV` — every single modulus in the BV range obeys the AP-form
  Siegel–Walfisz bound (each summand of a non-negative sum is at most the sum);
* `apSW_of_OAIBV` — the standard AP-form Siegel–Walfisz statement for all moduli
  `q ≤ (log x)^B` and all reduced classes, derived from the external BV statement alone.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain.OAIImport

open Erdos287.CurrentTail

/-- `Λ` as a real-valued function. -/
noncomputable abbrev vonMangoldtR : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n

/-- **Exact dictionary.** `progSum (Ioc 0 N) Λ q a = residuePrefix Λ N q (a % q)`. -/
theorem progSum_vonMangoldt_eq_residuePrefix (N q a : ℕ) :
    progSum (Finset.Ioc 0 N) vonMangoldtR q a =
      residuePrefix (fun n => ArithmeticFunction.vonMangoldt n) N q (a % q) := by
  unfold progSum residuePrefix residueSlice
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Nat.ModEq]

/-- **Exact dictionary for the endpoint error.** -/
theorem abs_progErr_le_endpointError (x : ℝ) {q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    |progErr (Finset.Ioc 0 ⌊x⌋₊) vonMangoldtR x q a| ≤ (endpointError x q : ℝ) := by
  have hc : a % q < q := Nat.mod_lt _ hq
  have hcop : Nat.Coprime (a % q) q := by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  let F : ℕ → NNReal := fun c => if Nat.Coprime c q then
    (⟨|residuePrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊x⌋₊ q c -
      x / q.totient|, abs_nonneg _⟩ : NNReal) else 0
  have h : F (a % q) ≤ (Finset.range q).sup F := Finset.le_sup (Finset.mem_range.mpr hc)
  have hF : F (a % q) = ⟨|residuePrefix (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      ⌊x⌋₊ q (a % q) - x / q.totient|, abs_nonneg _⟩ := if_pos hcop
  rw [hF] at h
  unfold progErr
  rw [progSum_vonMangoldt_eq_residuePrefix]
  exact NNReal.coe_le_coe.mpr h

/-- The external BV statement in project notation, maximal over reduced residues. -/
def PsiBVProjectForm : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ r : ℕ → ℕ, (∀ q, Nat.Coprime (r q) q) →
      ∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        |progErr (Finset.Ioc 0 ⌊x⌋₊) vonMangoldtR x q (r q)| ≤ M*x*(Real.log x)^(-A)

/-- **External BV ⟹ project-notation maximal BV** (exact adapter). -/
theorem psiBVProjectForm_of_OAI (h : OAIBombieriVinogradov) : PsiBVProjectForm := by
  intro A hA
  obtain ⟨b, hb, M, hM, x₀, hx₀, hbv⟩ := h A hA
  refine ⟨b, hb, M, hM, x₀, hx₀, fun x hx r hr => le_trans ?_ (hbv x hx)⟩
  refine Finset.sum_le_sum (fun q hq => ?_)
  exact abs_progErr_le_endpointError x (Finset.mem_Icc.1 hq).1 (hr q)

/-- **Single modulus in the BV range** (from the external BV statement). -/
theorem tinyModulusSW_of_OAIBV (h : OAIBombieriVinogradov) :
    ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ x^(1/2:ℝ) * (Real.log x)^(-b) →
        ∀ a : ℕ, Nat.Coprime a q →
          |progErr (Finset.Ioc 0 ⌊x⌋₊) vonMangoldtR x q a| ≤ M*x*(Real.log x)^(-A) := by
  intro A hA
  obtain ⟨b, hb, M, hM, x₀, hx₀, hbv⟩ := h A hA
  refine ⟨b, hb, M, hM, x₀, hx₀, fun x hx q hq hqx a ha => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hmem : q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊ :=
    Finset.mem_Icc.2 ⟨hq, Nat.le_floor hqx⟩
  calc |progErr (Finset.Ioc 0 ⌊x⌋₊) vonMangoldtR x q a| ≤ (endpointError x q : ℝ) :=
        abs_progErr_le_endpointError x hq ha
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊, (endpointError x q : ℝ) :=
        Finset.single_le_sum (f := fun q => (endpointError x q : ℝ))
          (fun _ _ => NNReal.coe_nonneg _) hmem
    _ ≤ _ := hbv x hx

/-- Eventually `(log x)^B ≤ x^{1/2} (log x)^{-b}`. -/
theorem eventually_logpow_le_sqrt_mul (B b : ℝ) :
    ∃ x₁ : ℝ, 1 < x₁ ∧ ∀ x : ℝ, x₁ ≤ x →
      (Real.log x)^B ≤ x^(1/2:ℝ) * (Real.log x)^(-b) := by
  have hlo := isLittleO_log_rpow_rpow_atTop (B + b) (show (0:ℝ) < 1/2 by norm_num)
  have hev := hlo.bound (show (0:ℝ) < 1 by norm_num)
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, (Real.exp 1 ≤ x ∧
      ‖Real.log x ^ (B + b)‖ ≤ 1 * ‖x ^ (1/2:ℝ)‖) :=
    (Filter.eventually_ge_atTop _).and hev
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hev2
  refine ⟨max x₁ 3, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  obtain ⟨he, hb⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hL0 : 0 < Real.log x := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hb
  have hpos : 0 < (Real.log x)^b := Real.rpow_pos_of_pos hL0 _
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hpos, ← Real.rpow_add hL0]
  exact hb

/-- **AP-form Siegel–Walfisz from the external BV statement.**  For every `A, B > 0` there are
`M, x₀` such that for `x ≥ x₀`, every modulus `1 ≤ q ≤ (log x)^B` and every reduced class `a`,
`|ψ(x; q, a) - x/φ(q)| ≤ M x (log x)^{-A}` (in project notation). -/
theorem apSW_of_OAIBV (h : OAIBombieriVinogradov) :
    ∀ A B : ℝ, 0 < A → 0 < B → ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x)^B →
        ∀ a : ℕ, Nat.Coprime a q →
          |progErr (Finset.Ioc 0 ⌊x⌋₊) vonMangoldtR x q a| ≤ M*x*(Real.log x)^(-A) := by
  intro A B hA _
  obtain ⟨b, _, M, hM, x₀, hx₀, hsw⟩ := tinyModulusSW_of_OAIBV h A hA
  obtain ⟨x₁, hx₁, hle⟩ := eventually_logpow_le_sqrt_mul B b
  refine ⟨M, hM, max x₀ x₁, lt_of_lt_of_le hx₀ (le_max_left _ _), fun x hx q hq hqB a ha => ?_⟩
  exact hsw x ((le_max_left _ _).trans hx) q hq
    (hqB.trans (hle x ((le_max_right _ _).trans hx))) a ha

end Erdos287.SourceChain.OAIImport
