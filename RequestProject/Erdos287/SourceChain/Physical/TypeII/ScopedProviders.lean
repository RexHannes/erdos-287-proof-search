import RequestProject.Erdos287.SourceChain.Physical.TypeII.RemainingProviders

/-!
# Erdős #287 — parameter ledger and correctly scoped (still UNPROVED) Type-II providers

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.  The two `…Scoped` providers below are
UNPROVED analytic inputs**, exactly like the providers in `RemainingProviders.lean`.  What is
proved here is

* the **exponent ledger** (`ε = κ/2000`, `σ = κ/10⁶`, `δ_spec = σ/4`):
  `old_packet_margin_neg` (the old cap `f ≤ X^{κ/1000}` gives the negative margin
  `-327κ/256000`), `new_packet_margin_eq` / `new_packet_margin_pos`
  (`ε/2 - (391/256)σ = 63609κ/256000000 > 0`), `sigmaBase_le_eps_div_100`,
  `two_deltaSpec_lt_sigma`;
* **repaired interfaces**: `PascadiCriticalCellProviderScoped` and `OrdinaryBVUremProviderScoped`
  fix admissible affine data `A > 0`, `B ≠ 0`, `gcd(A,|B|) = 1` and a roughness exponent
  **before** the constants are chosen, cap the base by `f ≤ X^σ` with `σ = κ/10⁶`, require the
  product scale `X ≤ 4 N M` (i.e. `x ≍ MN`), roughness of `α`, and the Siegel–Walfisz condition
  with a coprimality mask (`SWSeqMasked`);
* `pascadi_scoped_of_old`, `bvUrem_scoped_of_old` — each old provider implies the scoped one
  (so the scoped providers are *weaker* statements; nothing is lost);
* `scalarTypeII_bound_of_scopedProviders` — the composed scalar Type-II bound from the scoped
  providers, on the restricted (actual-source) range.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-! ### Exponent ledger -/

/-- Kernel exponent exported by `physAtom_provider_contract`. -/
noncomputable def epsKernel (κ : ℝ) : ℝ := κ / 2000

/-- Repaired base-support exponent. -/
noncomputable def sigmaBase (κ : ℝ) : ℝ := κ / 1000000

/-- Spectator exponent. -/
noncomputable def deltaSpec (κ : ℝ) : ℝ := sigmaBase κ / 4

/-- With the old cap `σ_old = κ/1000` the packet margin is negative. -/
theorem old_packet_margin_eq (κ : ℝ) :
    epsKernel κ / 2 - 391 / 256 * (κ / 1000) = -(327 / 256000) * κ := by
  unfold epsKernel; ring

theorem old_packet_margin_neg {κ : ℝ} (hκ : 0 < κ) :
    epsKernel κ / 2 - 391 / 256 * (κ / 1000) < 0 := by
  rw [old_packet_margin_eq]; linarith

theorem new_packet_margin_eq (κ : ℝ) :
    epsKernel κ / 2 - 391 / 256 * sigmaBase κ = 63609 / 256000000 * κ := by
  unfold epsKernel sigmaBase; ring

theorem new_packet_margin_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < epsKernel κ / 2 - 391 / 256 * sigmaBase κ := by
  rw [new_packet_margin_eq]; positivity

theorem sigmaBase_le_eps_div_100 {κ : ℝ} (hκ : 0 ≤ κ) : sigmaBase κ ≤ epsKernel κ / 100 := by
  unfold sigmaBase epsKernel; linarith

theorem two_deltaSpec_lt_sigma {κ : ℝ} (hκ : 0 < κ) : 2 * deltaSpec κ < sigmaBase κ := by
  unfold deltaSpec sigmaBase; linarith

theorem sigmaBase_le_old_cap {κ : ℝ} (hκ : 0 ≤ κ) : sigmaBase κ ≤ κ / 1000 := by
  unfold sigmaBase; linarith

/-- The new base cap implies the old one (`X ≥ 1`). -/
theorem base_cap_mono {κ X f : ℝ} (hκ : 0 ≤ κ) (hX : 1 ≤ X) (hf : f ≤ X ^ sigmaBase κ) :
    f ≤ X ^ (κ / 1000) :=
  hf.trans (Real.rpow_le_rpow_of_exponent_le hX (sigmaBase_le_old_cap hκ))

/-! ### Siegel–Walfisz with a coprimality mask, roughness -/

open Classical in
/-- Siegel–Walfisz condition with an additional coprimality mask `(n, d) = 1` (all `d ≥ 1`),
in the relative-centering form `∑_{n ≡ a (q), (n,d)=1} α - φ(q)⁻¹ ∑_{(n,qd)=1} α`. -/
def SWSeqMasked (α : ArithmeticFunction ℝ) (Nn : ℕ) (Aexp B C : ℝ) : Prop :=
  ∀ d q a : ℕ, 0 < d → 0 < q → (q : ℝ) ≤ Real.log Nn ^ B → Nat.Coprime a q →
    |∑ n ∈ range (2 * Nn), (if n ≡ a [MOD q] ∧ Nat.Coprime n d then α n else 0) -
      (1 / (Nat.totient q : ℝ)) *
        ∑ n ∈ range (2 * Nn), (if Nat.Coprime n (q * d) then α n else 0)|
      ≤ C * Nn / Real.log Nn ^ Aexp

/-- The masked condition with `d = 1` is the unmasked `SWSeq`. -/
theorem SWSeq_of_masked {α : ArithmeticFunction ℝ} {Nn : ℕ} {Aexp B C : ℝ}
    (h : SWSeqMasked α Nn Aexp B C) : SWSeq α Nn Aexp B C := by
  classical
  intro q a hq hqB hcop
  have := h 1 q a one_pos hq hqB hcop
  simpa [Nat.coprime_one_right] using this

/-- `α` is supported on `z`-rough integers (no prime factor below `z`). -/
def RoughSupport (α : ArithmeticFunction ℝ) (z : ℝ) : Prop :=
  ∀ m, α m ≠ 0 → ∀ p : ℕ, p.Prime → p ∣ m → z ≤ p

/-! ### Scoped providers (UNPROVED analytic inputs) -/

/-- **(UNPROVED) Scoped Pascadi critical-cell estimate.**  Affine data `A > 0`, `B ≠ 0`,
`gcd(A, |B|) = 1` and a roughness exponent `ρ > 0` are fixed first; the constants may depend
on them.  Base cap `f ≤ X^{κ/10⁶}`, product scale `X/4 ≤ N M ≤ X`, `α` is `X^ρ`-rough and
masked-SW. -/
def PascadiCriticalCellProviderScoped (κ : ℝ) : Prop :=
  ∀ (A : ℕ) (Bres : ℤ), 0 < A → Bres ≠ 0 → Nat.Coprime A Bres.natAbs → ∀ ρ : ℝ, 0 < ρ →
  ∀ Aexp Csw : ℝ, ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K n : ℕ), K ≤ 2 ^ n → 0 < f → (f : ℝ) ≤ S.X ^ sigmaBase κ →
    Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
    ∀ (J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3), S.BoxAdm J P →
      |∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S κ Nn Γ f c A Bres K (2 ^ i) (2 ^ i') Nn M J P χ α β).T| ≤
        C * Bα * Bβ * |Γ| * S.atomWeight J P (S.atomColour κ Nn J P) * S.X /
          (f * Real.log S.X ^ Aexp)

/-- **(UNPROVED) Scoped ordinary-range bound for the `h_l U_r` part**: same fixed data and
ranges as above, and — unlike `OrdinaryBVUremProvider` — a distribution (masked SW) hypothesis
on `α`. -/
def OrdinaryBVUremProviderScoped (κ : ℝ) : Prop :=
  ∀ (A : ℕ) (Bres : ℤ), 0 < A → Bres ≠ 0 → Nat.Coprime A Bres.natAbs → ∀ ρ : ℝ, 0 < ρ →
  ∀ Aexp Csw A' B : ℝ, ∃ C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K K' : ℕ), 0 < f → (f : ℝ) ≤ S.X ^ sigmaBase κ →
    Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
      |physUrem S κ Nn Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp)

/-- The old (over-broad) Pascadi provider implies the scoped one. -/
theorem pascadi_scoped_of_old {κ : ℝ} (h : PascadiCriticalCellProvider κ) :
    PascadiCriticalCellProviderScoped κ := by
  intro A Bres _ _ _ ρ _ Aexp Csw
  obtain ⟨A', B, C, X0, hP⟩ := h Aexp Csw
  refine ⟨A', B, C, X0, ?_⟩
  intro S hreg hX Nn M hN hNM _ Γ f c K n hKn hf0 hf hcf α β Bα Bβ hαb hβb hα hβ _ hsw
  exact hP S hreg hX Nn M hN hNM Γ f c A Bres K n hKn hf0
    (base_cap_mono hreg.κ_pos.le hreg.good.X_gt.le hf) hcf α β Bα Bβ hαb hβb hα hβ
    (SWSeq_of_masked hsw)

/-- The old (over-broad) `U`-remainder provider implies the scoped one. -/
theorem bvUrem_scoped_of_old {κ : ℝ} (h : OrdinaryBVUremProvider κ) :
    OrdinaryBVUremProviderScoped κ := by
  intro A Bres _ _ _ ρ _ Aexp Csw A' B
  obtain ⟨C, X0, hU⟩ := h Aexp
  refine ⟨C, X0, ?_⟩
  intro S hreg hX Nn M hN hNM _ Γ f c K K' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ _ _
  exact hU S hreg hX Nn M hN hNM Γ f c A Bres K K' hf0
    (base_cap_mono hreg.κ_pos.le hreg.good.X_gt.le hf) hcf α β Bα Bβ hαb hβb hα hβ

/-- **The actual critical scalar Type-II source under the two scoped providers**, on the
restricted actual-source range (fixed admissible affine data, `f ≤ X^{κ/10⁶}`, `X ≤ 4NM`,
rough masked-SW `α`). -/
theorem scalarTypeII_bound_of_scopedProviders {κ : ℝ}
    (hP4 : PascadiCriticalCellProviderScoped κ) (hBV : OrdinaryBVUremProviderScoped κ)
    (A : ℕ) (Bres : ℤ) (hA : 0 < A) (hB : Bres ≠ 0) (hAB : Nat.Coprime A Bres.natAbs)
    (ρ : ℝ) (hρ : 0 < ρ) (Aexp Csw : ℝ) :
    ∃ A' B C X0 : ℝ, ∀ S : ScalarParams, CritRegime S κ → X0 ≤ S.X →
    ∀ Nn M : ℕ, CritCell S κ Nn → (Nn : ℝ) * M ≤ S.X → S.X ≤ 4 * ((Nn : ℝ) * M) →
    ∀ (Γ : ℝ) (f c : ℕ) (K n K' : ℕ), K ≤ 2 ^ n → 4 * Nn * M ≤ K' → 0 < f →
    (f : ℝ) ≤ S.X ^ sigmaBase κ → Nat.Coprime c f →
    ∀ (α β : ArithmeticFunction ℝ) (Bα Bβ : ℝ), (∀ m, |α m| ≤ Bα) → (∀ m, |β m| ≤ Bβ) →
    (∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) → (∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M) →
    RoughSupport α (S.X ^ ρ) → SWSeqMasked α Nn A' B (Csw * Bα) →
      |scalarTypeII S Γ f c A Bres K K' α β| ≤
        C * Bα * Bβ * |Γ| * (∑ J ∈ range (S.T ^ 2 + 1), (S.H : ℝ) ^ J * 3 ^ J) * S.X /
          (f * Real.log S.X ^ Aexp) := by
  obtain ⟨A', B, C1, X1, h1⟩ := hP4 A Bres hA hB hAB ρ hρ Aexp Csw
  obtain ⟨C2, X2, h2⟩ := hBV A Bres hA hB hAB ρ hρ Aexp Csw A' B
  refine ⟨A', B, |C1| + C2, max X1 X2, ?_⟩
  intro S hreg hX Nn M hN hNM hNM' Γ f c K n K' hKn hK' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ
    hrough hsw
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
    refine (h1 S hreg hX1 Nn M hN hNM hNM' Γ f c K n hKn hf0 hf hcf α β Bα Bβ hαb hβb hα hβ
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
  · exact h2 S hreg hX2 Nn M hN hNM hNM' Γ f c K K' hf0 hf hcf α β Bα Bβ hαb hβb hα hβ
      hrough hsw

end Erdos287.Physical.TypeII
