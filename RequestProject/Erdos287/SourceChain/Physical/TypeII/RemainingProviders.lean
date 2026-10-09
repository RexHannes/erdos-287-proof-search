import RequestProject.Erdos287.SourceChain.Physical.TypeII.SourceComposed

/-!
# Erdős #287 — remaining analytic providers for the actual Type-II source

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  Nothing in this file is proved about
primes: every `def … : Prop` below is an UNPROVED analytic input, stated in full.**

The source side is closed by `scalarTypeII_eq_cells` / `physCell_contract`.  What remains for
the *critical* Type-II part of the actual source is:

* `PascadiCriticalCellProvider κ` — **Pascadi's beyond-half estimate** for the actual critical
  cells.  The moduli `l r` reach `D_tot = X^{59/100} > X^{1/2}`, so ordinary BV/BDH does **not**
  supply it.
* `OrdinaryBVUremProvider κ` — the `h_l U_r` part: only the modulus `f l` with
  `l ≤ N X^{-κ} ≤ X^{1/3}` carries a congruence, so this is an **ordinary** BV/BDH-range input
  (level below `1/2`).
* `SWSeq` — the Siegel–Walfisz condition on the smooth-variable sequence `α`, used as a
  hypothesis inside `PascadiCriticalCellProvider` (as in every Bombieri–Vinogradov-type
  bilinear estimate).

`scalarTypeII_bound_of_cells` is the kernel-proved composition: per-atom cell bounds plus a bound
on `physUrem` give a bound on the scalar Type-II source, with the atom total variation
`∑_{J ≤ T²} H^J 3^J` (independent of `X`).  `scalarTypeII_bound_of_providers` instantiates it
with the two providers.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

open Classical in
/-- Siegel–Walfisz condition for a sequence supported on `[N, 2N)`, moduli `q ≤ (log N)^B`. -/
def SWSeq (α : ArithmeticFunction ℝ) (Nn : ℕ) (Aexp B C : ℝ) : Prop :=
  ∀ q a : ℕ, 0 < q → (q : ℝ) ≤ Real.log Nn ^ B → Nat.Coprime a q →
    |∑ n ∈ range (2 * Nn), (if n ≡ a [MOD q] then α n else 0) -
      (1 / (Nat.totient q : ℝ)) * ∑ n ∈ range (2 * Nn), (if Nat.Coprime n q then α n else 0)|
      ≤ C * Nn / Real.log Nn ^ Aexp

/-- **(UNPROVED) Pascadi's beyond-half estimate, at the actual critical Type-II cells.**
For every saving exponent `A` and every Siegel–Walfisz constant `C_SW` there are a
Siegel–Walfisz strength `A'`, a modulus range `(log N)^B`, and `C, X₀` such that for every scalar parameter set in the
small-`ε₀` regime of `κ`, every critical cell `N_n`, `N_n M ≤ X`, every packet modulus
`f ≤ X^{κ/1000}` with `(c, f) = 1`, every sequence pair `α ∼ N_n`, `β ∼ M` with `|α| ≤ B_α`,
`|β| ≤ B_β` and `α` Siegel–Walfisz, and every admissible sector `(J, P)` and colouring `χ`,
the dyadically summed cells of the atom are bounded by
`C B_α B_β |Γ| w_{J,P} X / (f (log X)^A)`. -/
def PascadiCriticalCellProvider (κ : ℝ) : Prop :=
  ∀ Aexp Csw : ℝ, ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
    ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K n : ℕ), K ≤ 2 ^ n → 0 < f → (f : ℝ) ≤ S.X ^ (κ / 1000) →
    Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    SWSeq α Nn A' B (Csw * Bα) →
    ∀ (J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3), S.BoxAdm J P →
      |∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S κ Nn Γ f c A Bres K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
        C * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * S.X /
          (f * Real.log S.X ^ Aexp)

/-- **(UNPROVED) Ordinary BV/BDH-range bound for the `h_l U_r` part** of the actual
critical Type-II source (only `f l`, `l ≤ X^{1/3}`, carries a congruence). -/
def OrdinaryBVUremProvider (κ : ℝ) : Prop :=
  ∀ Aexp : ℝ, ∃ C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
    ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K K' : ℕ), 0 < f → (f : ℝ) ≤ S.X ^ (κ / 1000) →
    Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
      |physUrem S κ Nn Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp)

variable {S : ScalarParams}

/-- Non-admissible sectors contribute nothing. -/
theorem physCell_T_eq_zero {δ N Γ : ℝ} {f c A : ℕ} {B : ℤ} {K L R Nn M J : ℕ}
    {P : Fin J → Fin S.H} (hP : ¬ S.BoxAdm J P) (χ : Fin S.Kc → Fin 3)
    (α β : ArithmeticFunction ℝ) :
    (physCell S δ N Γ f c A B K L R Nn M J P χ α β).T = 0 := by
  classical
  simp [OBData.T, OBData.inner, physCell, physCoefCut, physCoefAtom, hP]

/-- **Kernel-proved composition**: per-atom bounds on the dyadically summed cells and a bound
on `physUrem` bound the whole scalar Type-II source. -/
theorem scalarTypeII_bound_of_cells (hS : S.Good) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) {K n : ℕ}
    (hKn : K ≤ 2 ^ n) {Nn M K' : ℕ} (α β : ArithmeticFunction ℝ)
    (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    (hK' : 4 * Nn * M ≤ K') {E EU : ℝ} (hE : 0 ≤ E)
    (hcell : ∀ (J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3), S.BoxAdm J P →
      |∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
        |Γ| * S.atomWeight J P (S.atomColour δ N J P) * E)
    (hU : |physUrem S δ N Γ f c A B K K' α β| ≤ EU) :
    |scalarTypeII S Γ f c A B K K' α β| ≤
      |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * E + EU := by
  classical
  rw [scalarTypeII_eq_cells hS δ N Γ f c A B hKn α β hα hβ hK']
  refine (abs_add_le _ _).trans (add_le_add ?_ hU)
  have htv := total_variation_le (S := S) (S.atomColour δ N)
  have step : |∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
      ∑ i ∈ range n, ∑ i' ∈ range n,
        (physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H,
        (if S.BoxAdm J P then ∑ _χ : Fin S.Kc → Fin 3,
          |(-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P)| else 0) * (|Γ| * E) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun J _ => ?_))
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun P _ => ?_))
    refine (abs_sum_le_sum_abs _ _).trans ?_
    by_cases hP : S.BoxAdm J P
    · rw [if_pos hP, sum_mul]
      refine sum_le_sum (fun χ _ => ?_)
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (atomWeight_nonneg P _)]
      refine (hcell J P χ hP).trans (le_of_eq ?_)
      ring
    · rw [if_neg hP, zero_mul]
      refine le_of_eq (sum_eq_zero (fun χ _ => ?_))
      rw [abs_eq_zero]
      exact sum_eq_zero (fun i _ => sum_eq_zero (fun i' _ => physCell_T_eq_zero hP χ α β))
  refine step.trans ?_
  simp_rw [← sum_mul]
  have hΓE : 0 ≤ |Γ| * E := mul_nonneg (abs_nonneg _) hE
  calc (∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H,
        (if S.BoxAdm J P then ∑ _χ : Fin S.Kc → Fin 3,
          |(-1 : ℝ) ^ J * S.atomWeight J P (S.atomColour δ N J P)| else 0)) * (|Γ| * E)
      ≤ (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * (|Γ| * E) :=
        mul_le_mul_of_nonneg_right htv hΓE
    _ = _ := by ring

/-- **The actual critical scalar Type-II source under the two named providers.**
For every `A` and `C_SW` there are `A', B, C, X₀` such that, in the small-`ε₀` regime and on critical cells,
`|scalarTypeII| ≤ C B_α B_β |Γ| (∑_{J ≤ T²} H^J 3^J) X / (f (log X)^A)`. -/
theorem scalarTypeII_bound_of_providers {κ : ℝ} (hP4 : PascadiCriticalCellProvider κ)
    (hBV : OrdinaryBVUremProvider κ) (Aexp Csw : ℝ) :
    ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X →
    ∀ (Γ : ℝ) (f c A : ℕ) (Bres : ℤ) (K n K' : ℕ), K ≤ 2 ^ n → 4 * Nn * M ≤ K' → 0 < f →
    (f : ℝ) ≤ S.X ^ (κ / 1000) → Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    SWSeq α Nn A' B (Csw * Bα) →
      |scalarTypeII S Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp) := by
  obtain ⟨A', B, C1, X1, h1⟩ := hP4 Aexp Csw
  obtain ⟨C2, X2, h2⟩ := hBV Aexp
  refine ⟨A', B, |C1| + C2, max X1 X2, ?_⟩
  intro S hreg hX Nn M hN hNM Γ f c A Bres K n K' hKn hK' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hsw
  have hX1 : X1 ≤ S.X := le_trans (le_max_left _ _) hX
  have hX2 : X2 ≤ S.X := le_trans (le_max_right _ _) hX
  have hBα : 0 ≤ Bα := le_trans (abs_nonneg _) (hαb 0)
  have hBβ : 0 ≤ Bβ := le_trans (abs_nonneg _) (hβb 0)
  set E : ℝ := |C1| * Bα * Bβ * S.X / (f * Real.log S.X ^ Aexp) with hEdef
  have hXpos : 0 < S.X := by linarith [hreg.good.X_gt]
  have hlog : 0 ≤ Real.log S.X := Real.log_nonneg hreg.good.X_gt.le
  have hden : 0 ≤ (f : ℝ) * Real.log S.X ^ Aexp :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hlog _)
  have hE : 0 ≤ E := div_nonneg (by positivity) hden
  have key := scalarTypeII_bound_of_cells hreg.good κ (Nn : ℝ) Γ f c A Bres hKn α β hα hβ hK'
    hE (EU := C2 * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp)) ?_ ?_
  · refine key.trans (le_of_eq ?_)
    simp only [hEdef]
    ring
  · intro J P χ hP
    refine (h1 S hreg hX1 Nn M hN hNM Γ f c A Bres K n hKn hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hsw
      J P χ hP).trans ?_
    simp only [hEdef]
    have hw := atomWeight_nonneg P (S.atomColour κ Nn J P)
    rw [mul_div_assoc, mul_div_assoc]
    have hq : 0 ≤ S.X / (f * Real.log S.X ^ Aexp) := div_nonneg hXpos.le hden
    have : C1 * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) ≤
        |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * (|C1| * Bα * Bβ) := by
      have hc : C1 ≤ |C1| := le_abs_self C1
      have : 0 ≤ Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) := by positivity
      nlinarith
    calc C1 * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) *
          (S.X / (f * Real.log S.X ^ Aexp))
        ≤ |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * (|C1| * Bα * Bβ) *
          (S.X / (f * Real.log S.X ^ Aexp)) := mul_le_mul_of_nonneg_right this hq
      _ = _ := by ring
  · exact h2 S hreg hX2 Nn M hN hNM Γ f c A Bres K K' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ

end Erdos287.Physical.TypeII
