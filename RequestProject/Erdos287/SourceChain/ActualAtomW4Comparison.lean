import RequestProject.Erdos287.SourceChain.W4Route
import RequestProject.Erdos287.SourceChain.NarrowTail
import RequestProject.Erdos287.SourceChain.CrossCoprime

/-!
# Erdős #287 — Astra vs V101 actual-atom routes, degenerate cells, and the atom-level tail

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**
`AstraActualAtomW4 = PaperCandidate`, `V101ActualAtomW4 = PaperCandidate`,
`Tail287 = KernelConditional`, `IndependentAudit = Pending`.  These labels are data only; no
declaration turns them into an analytic theorem.

* `Route`, `routeKernelExp`, `routeFinalExp`, `route_final_of_kernel` — the comparison table,
  kernel-checked: final exponent `= (kernel + 1)/2` for both routes.
* `DegenerateCell`, `degenerateRouting`, `no_retired_shortcut` — short-`H` / degenerate-factor
  status datatype; no case routes to the retired "factor `= 1` ⟹ modulus `< 1/2`" shortcut.
* `AstraAtomBound` — the per-packet actual-atom estimate at the Astra weak target
  (`|𝒦| ≤ C₀ f^{263/128} N²/(Q x^ε)`, `F^♯ = (M/f)𝒦`, `𝓑 ≤ MQ(log x)^{C}`).
* `sharpPowerSaving_of_atom` — actual-atom estimate + `f ≤ x^σ` + `391σ/256 < ε/2` ⟹ fixed power
  saving of the clean-AA cell; `sharpPaid_of_atom` adds the reciprocal packet norm.
* `Tail287_of_AtomProviders` — the conditional tail with the Astra atom estimate in place of
  `SharpMembership` + `PascadiSpectralY`.  Still conditional.
-/

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

/-! ### Route comparison -/

inductive Route | astra | v101
  deriving DecidableEq, Repr

inductive AuditStatus | PaperCandidate | Banked
  deriving DecidableEq, Repr

def routeKernelExp : Route → ℚ
  | .astra => 263 / 128
  | .v101 => 647 / 128

def routeFinalExp : Route → ℚ
  | .astra => 391 / 256
  | .v101 => 775 / 256

def routeStatus : Route → AuditStatus
  | _ => .PaperCandidate

theorem route_final_of_kernel : ∀ r : Route, routeFinalExp r = (routeKernelExp r + 1) / 2 := by
  intro r; cases r <;> norm_num [routeFinalExp, routeKernelExp]

theorem routes_not_banked : ∀ r : Route, routeStatus r = .PaperCandidate := by
  intro r; cases r <;> rfl

/-! ### Degenerate / short-`H` cells -/

inductive DegenerateCell
  | fourierTailOnly | boundedH | shortH0 | sOne | rOne | qOne | twoEmptyHigh
  deriving DecidableEq, Repr

inductive CellRouting
  | fourierTailDecay      -- `PF_decay_bound`
  | integerHGeOne         -- actual integer `H ≥ 1` kept; same `W₄` providers
  | boundedFactorCount    -- bounded factor ⟹ count absorbed (`aaShape_cell_bound`)
  | retiredShortcut       -- "factor = 1 ⟹ full modulus < 1/2" (RETIRED)
  deriving DecidableEq, Repr

def degenerateRouting : DegenerateCell → CellRouting
  | .fourierTailOnly => .fourierTailDecay
  | .boundedH => .integerHGeOne
  | .shortH0 => .integerHGeOne
  | .sOne => .boundedFactorCount
  | .rOne => .boundedFactorCount
  | .qOne => .boundedFactorCount
  | .twoEmptyHigh => .boundedFactorCount

theorem no_retired_shortcut : ∀ c : DegenerateCell, degenerateRouting c ≠ .retiredShortcut := by
  intro c; cases c <;> decide

/-! ### Actual-atom estimate ⟹ clean-AA payment -/

variable {ι : Type*}

/-- **Astra per-packet actual-atom estimate** (weak target). -/
def AstraAtomBound (x f Bc piece CK C0 ε : ℝ) : Prop :=
  ∃ M N Q K : ℝ, 0 < M ∧ 0 < N ∧ 0 < Q ∧ x = M * N ∧
    |K| ≤ C0 * f ^ ((263 : ℝ) / 128) * N ^ 2 / Q * x ^ (-ε) ∧
    piece = M / f * |K| ∧ Bc ≤ M * Q * Real.log x ^ CK

/-- **Actual-atom estimate ⟹ fixed power saving of the clean-AA cell.** -/
theorem sharpPowerSaving_of_atom {S : TailSourceFamily ι} (C : OrderingBCells S)
    (Fs : FamilyScale S) {σ ε CK C0 : ℝ} (hC0 : 0 ≤ C0)
    (hledger : 391 / 256 * σ < ε / 2)
    (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
      AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε) :
    PowerSavingCell S C Fs .sharp := by
  obtain ⟨X1, hX1⟩ := hatom
  obtain ⟨X2, hX2⟩ := Fs.x_large 3
  refine ⟨CK / 2, ε / 2 - 391 / 256 * σ, Real.sqrt C0, by linarith, Real.sqrt_nonneg _,
    max X1 X2, fun X hX ξ hξ => ?_⟩
  have hx3 : 3 ≤ Fs.x X := hX2 X (le_trans (le_max_right _ _) hX)
  have hx0 : 0 < Fs.x X := by linarith
  have hlog : 0 ≤ Real.log (Fs.x X) := Real.log_nonneg (by linarith)
  obtain ⟨hfσ, M, N, Q, K, hM, hN, hQ, hx, hK, hpiece, hB⟩ :=
    hX1 X (le_trans (le_max_left _ _) hX) ξ hξ
  have hf1 : (1 : ℝ) ≤ (S.T X).f ξ := by exact_mod_cast (S.T X).f_pos ξ hξ
  have hf : (0 : ℝ) < (S.T X).f ξ := by linarith
  have hL : 0 ≤ Real.log (Fs.x X) ^ CK := Real.rpow_nonneg hlog _
  have hpk := astra_packet_391 (K := |K|) (Fsh := M / ((S.T X).f ξ) * |K|) hM hN hQ hf hC0 hL hx
    (by rwa [abs_abs]) rfl hB
  have habs : abs (M / ((S.T X).f ξ) * |K|) = C.piece X ξ .sharp := by
    rw [hpiece]; exact abs_of_nonneg (by positivity)
  rw [habs] at hpk
  refine hpk.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hfp : ((S.T X).f ξ : ℝ) ^ ((391 : ℝ) / 256) ≤ Fs.x X ^ (391 / 256 * σ) := by
    calc ((S.T X).f ξ : ℝ) ^ ((391 : ℝ) / 256) ≤ (Fs.x X ^ σ) ^ ((391 : ℝ) / 256) :=
          Real.rpow_le_rpow hf.le hfσ (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hx0.le]; ring_nf
  have hsq : Real.sqrt (C0 * Real.log (Fs.x X) ^ CK) =
      Real.sqrt C0 * Real.log (Fs.x X) ^ (CK / 2) := by
    rw [Real.sqrt_mul hC0, Real.sqrt_eq_rpow (Real.log (Fs.x X) ^ CK), ← Real.rpow_mul hlog]
    ring_nf
  rw [hsq]
  calc ((S.T X).f ξ : ℝ) ^ ((391 : ℝ) / 256) * Fs.x X ^ (-(ε / 2)) *
        (Real.sqrt C0 * Real.log (Fs.x X) ^ (CK / 2))
      ≤ Fs.x X ^ (391 / 256 * σ) * Fs.x X ^ (-(ε / 2)) *
        (Real.sqrt C0 * Real.log (Fs.x X) ^ (CK / 2)) := by gcongr
    _ = Real.sqrt C0 * Real.log (Fs.x X) ^ (CK / 2) * Fs.x X ^ (-(ε / 2 - 391 / 256 * σ)) := by
        have e : Fs.x X ^ (-(ε / 2 - 391 / 256 * σ)) =
            Fs.x X ^ (391 / 256 * σ) * Fs.x X ^ (-(ε / 2)) := by
          rw [← Real.rpow_add hx0]; ring_nf
        rw [e]; ring

/-- **Actual-atom estimate + reciprocal packet norm ⟹ clean-AA aggregate payment.** -/
theorem sharpPaid_of_atom {S : TailSourceFamily ι} (C : OrderingBCells S) (Fs : FamilyScale S)
    {CD σ ε CK C0 : ℝ} (hspec : SpectatorReciprocalNorm S Fs CD) (hC0 : 0 ≤ C0)
    (hledger : 391 / 256 * σ < ε / 2)
    (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
      AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε) :
    PiecePaid S C .sharp :=
  piecePaid_of_powerSaving C Fs hspec .sharp (sharpPowerSaving_of_atom C Fs hC0 hledger hatom)

/-- **Conditional tail theorem with the Astra actual-atom estimate.**  NOT unconditional. -/
theorem Tail287_of_AtomProviders (S : TailSourceFamily ι) (C : OrderingBCells S)
    (Fs : FamilyScale S) {CD σ ε CK C0 : ℝ}
    (Fw : SevenBlockTailFramework S) (hBase : BaseSWProvider S) (hCop : CoprimalityPaid S)
    (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
    (hspec : SpectatorReciprocalNorm S Fs CD) (hC0 : 0 ≤ C0)
    (hledger : 391 / 256 * σ < ε / 2)
    (hatom : ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
      ((S.T X).f ξ : ℝ) ≤ Fs.x X ^ σ ∧
      AstraAtomBound (Fs.x X) ((S.T X).f ξ) (C.Bc X ξ) (C.piece X ξ .sharp) CK C0 ε)
    (hOther : ∀ p, p ≠ CellPiece.sharp → PiecePaid S C p) : Tail287Statement := by
  refine Tail287_of_MinimalAnalyticProviders S C Fw hBase hCop hRed hCent (fun p => ?_)
  by_cases hp : p = CellPiece.sharp
  · subst hp; exact sharpPaid_of_atom C Fs hspec hC0 hledger hatom
  · exact hOther p hp

end Erdos287.SourceChain
