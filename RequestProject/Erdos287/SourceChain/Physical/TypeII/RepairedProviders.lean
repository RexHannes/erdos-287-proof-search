import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremCounterexample

/-!
# Erdős #287 — repaired (still UNPROVED) Type-II provider statements

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  The two `…Repaired` providers below are
UNPROVED analytic inputs** (they are `Prop`-valued definitions, not axioms, and are only ever
used as explicit hypotheses).

`UremCounterexample.lean` proves `¬ OrdinaryBVUremProviderScoped κ` using two defects:

1. the Siegel–Walfisz parameters `A'`, `B` were chosen by the *caller* (so `B = 0` made the
   distribution hypothesis vacuous);
2. nothing forced the primes of the affine pair `A · |B|` to divide the base `f`, so a modulus
   sharing a prime with `B` survived and did not cancel.

The repair, applied to both providers:

* the **provider** chooses the Siegel–Walfisz parameters (`∃ A' B` after the affine data,
  roughness exponent, target exponent `Aexp` and SW constant `Csw` are fixed);
* a new hypothesis `AffinePrimesDivideBase A Bres f`: every prime dividing `A · |Bres|`
  divides `f`.

Proved here:

* `uremCE_data_not_admissible` — the counterexample data `A = 1`, `B = 3`, `f = 2` violate the
  new hypothesis, so the refutation in `UremCounterexample.lean` does not apply;
* `physData_affinePrimesDivideBase` — the actual physical packets (`j ≠ ℓ`) satisfy it;
* `pascadi_repaired_of_scoped`, `bvUrem_repaired_of_scoped` — each repaired provider is implied
  by the corresponding scoped provider (so the repaired statements are weaker);
* `scalarTypeII_bound_of_repairedProviders` — the composed scalar Type-II bound from the two
  repaired providers.

Not proved (and not claimed): the repaired providers themselves.  They would need a
Bombieri–Vinogradov / beyond-half estimate for bilinear forms, which is not formalized.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-- Every prime dividing the reduced affine pair `A · |Bres|` divides the base `f`. -/
def AffinePrimesDivideBase (A : ℕ) (Bres : ℤ) (f : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ A * Bres.natAbs → p ∣ f

/-- The data used to refute `OrdinaryBVUremProviderScoped` (`A = 1`, `B = 3`, `f = 2`) are not
admissible for the repaired providers. -/
theorem uremCE_data_not_admissible : ¬ AffinePrimesDivideBase 1 3 2 := by
  intro h
  have := h 3 Nat.prime_three (by decide)
  omega

/-- The actual physical packets satisfy the new admissibility hypothesis. -/
theorem physData_affinePrimesDivideBase (P : Erdos287.Physical.PhysData) (hP : P.WGood)
    (ξ : Erdos287.Physical.Packet P.k) (hjl : ξ.j ≠ ξ.l) :
    AffinePrimesDivideBase (P.A ξ) (P.B ξ) (P.f ξ) :=
  fun _ hp hpAB => PhysData.prime_dvd_f_of_dvd_AB P hP ξ hjl hp hpAB

/-- **(UNPROVED) Repaired Pascadi critical-cell estimate**: `PascadiCriticalCellProviderScoped`
plus the hypothesis `AffinePrimesDivideBase A Bres f`. -/
def PascadiCriticalCellProviderRepaired (κ : ℝ) : Prop :=
  ∀ (A : ℕ) (Bres : ℤ), 0 < A → Bres ≠ 0 → Nat.Coprime A Bres.natAbs → ∀ ρ : ℝ, 0 < ρ →
  ∀ Aexp Csw : ℝ, ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K n : ℕ), K ≤ 2 ^ n → 0 < f → (f : ℝ) ≤ S.X ^ sigmaBase κ →
    Nat.Coprime c f → AffinePrimesDivideBase A Bres f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
    ∀ (J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3), S.BoxAdm J P →
      |∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S κ Nn Γ f c A Bres K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
        C * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * S.X /
          (f * Real.log S.X ^ Aexp)

/-- **(UNPROVED) Repaired ordinary-range bound for the `h_l U_r` part.**  Compared with
`OrdinaryBVUremProviderScoped` (which is false): the provider now chooses the Siegel–Walfisz
parameters `A'`, `B`, and every prime of `A · |Bres|` must divide `f`. -/
def OrdinaryBVUremProviderRepaired (κ : ℝ) : Prop :=
  ∀ (A : ℕ) (Bres : ℤ), 0 < A → Bres ≠ 0 → Nat.Coprime A Bres.natAbs → ∀ ρ : ℝ, 0 < ρ →
  ∀ Aexp Csw : ℝ, ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K K' : ℕ), 0 < f → (f : ℝ) ≤ S.X ^ sigmaBase κ →
    Nat.Coprime c f → AffinePrimesDivideBase A Bres f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
      |physUrem S κ Nn Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp)

/-- The scoped Pascadi provider implies the repaired one. -/
theorem pascadi_repaired_of_scoped {κ : ℝ} (h : PascadiCriticalCellProviderScoped κ) :
    PascadiCriticalCellProviderRepaired κ := by
  intro A Bres hA hB hAB ρ hρ Aexp Csw
  obtain ⟨A', B, C, X0, hP⟩ := h A Bres hA hB hAB ρ hρ Aexp Csw
  refine ⟨A', B, C, X0, ?_⟩
  intro S hreg hX Nn M hN hNM hNM' Γ f c K n hKn hf0 hf hcf _ α β Bα Bβ hαb hβb hα hβ hr hsw
  exact hP S hreg hX Nn M hN hNM hNM' Γ f c K n hKn hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hr hsw

/-- The scoped remainder provider implies the repaired one (the scoped one is false, so this
only records that the repaired statement is weaker). -/
theorem bvUrem_repaired_of_scoped {κ : ℝ} (h : OrdinaryBVUremProviderScoped κ) :
    OrdinaryBVUremProviderRepaired κ := by
  intro A Bres hA hB hAB ρ hρ Aexp Csw
  obtain ⟨C, X0, hU⟩ := h A Bres hA hB hAB ρ hρ Aexp Csw 0 0
  refine ⟨0, 0, C, X0, ?_⟩
  intro S hreg hX Nn M hN hNM hNM' Γ f c K K' hf0 hf hcf _ α β Bα Bβ hαb hβb hα hβ hr hsw
  exact hU S hreg hX Nn M hN hNM hNM' Γ f c K K' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ hr hsw

/-- **The critical scalar Type-II source under the two repaired providers** (each provider
supplies its own Siegel–Walfisz parameters, so both SW conditions are assumed). -/
theorem scalarTypeII_bound_of_repairedProviders {κ : ℝ}
    (hP4 : PascadiCriticalCellProviderRepaired κ) (hBV : OrdinaryBVUremProviderRepaired κ)
    (A : ℕ) (Bres : ℤ) (hA : 0 < A) (hB : Bres ≠ 0) (hAB : Nat.Coprime A Bres.natAbs)
    (ρ : ℝ) (hρ : 0 < ρ) (Aexp Csw : ℝ) :
    ∃ A' B A'' B'' C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K n K' : ℕ), K ≤ 2 ^ n → 4 * Nn * M ≤ K' → 0 < f →
    (f : ℝ) ≤ S.X ^ sigmaBase κ → Nat.Coprime c f → AffinePrimesDivideBase A Bres f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
    SWSeqMasked α Nn A'' B'' (Csw * Bα) →
      |scalarTypeII S Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp) := by
  obtain ⟨A', B, C1, X1, h1⟩ := hP4 A Bres hA hB hAB ρ hρ Aexp Csw
  obtain ⟨A'', B'', C2, X2, h2⟩ := hBV A Bres hA hB hAB ρ hρ Aexp Csw
  refine ⟨A', B, A'', B'', |C1| + C2, max X1 X2, ?_⟩
  intro S hreg hX Nn M hN hNM hNM' Γ f c K n K' hKn hK' hf0 hf hcf hfAB α β Bα Bβ hαb hβb hα hβ
    hrough hsw hsw'
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
    refine (h1 S hreg hX1 Nn M hN hNM hNM' Γ f c K n hKn hf0 hf hcf hfAB α β Bα Bβ hαb hβb hα hβ
      hrough hsw J P χ hP).trans ?_
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
  · exact h2 S hreg hX2 Nn M hN hNM hNM' Γ f c K K' hf0 hf hcf hfAB α β Bα Bβ hαb hβb hα hβ
      hrough hsw'

end Erdos287.Physical.TypeII
