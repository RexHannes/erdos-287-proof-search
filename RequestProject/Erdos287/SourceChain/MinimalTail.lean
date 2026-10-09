import RequestProject.Erdos287.CurrentTail
import RequestProject.Erdos287.SourceChain.CleanFAA

/-!
# Erdős #287 — source chain: Ordering-B cells, (REC.1) recombination and the minimal-provider tail

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  The theorem here is *conditional*.

This module replaces the monolithic `OrderingBSourceDictionary` (five fields with opaque
ledger pieces) and the monolithic `AuxPieceProviders` by:

1. **kernel-proved exact algebra**:
   * `RrelMain_eq_sum_Sxi` — `R_rel^main = ∑_ξ Γ_ξ S_ξ` with the literal packet component `S_ξ`;
   * `cell_bound` — the per-packet Ordering-B source inequality, together with
     `F_AB = F_AB^{k=1} + F_AB^{k>1}` (`FAB_split`) and `√(∑) ≤ ∑ √`, splits into the eight named
     cell pieces (`CellPiece`), each a norm of a **literal** object (`FABData.FABpart`,
     `FAAData.sector`, `FAAData.FAAsharp`) or the zero mode;
   * `RrelMain_bound` — (REC.1) at family level;
   * `RSigmaP_littleO_of_minimal` — V99 + coprimality + recombination;
2. **one source statement** `OrderingBPoissonReduction` (status `PAPER_VERIFIED_PARTIAL`): the
   per-packet inequality `|S_ξ| ≤ cent_ξ + √(𝓑_ξ (|F_AB,ξ| + ∑_{sectors}|F_s,ξ| + zm_ξ + |F^♯_ξ|))`
   produced by the Type-II split, first Cauchy, square expansion and Poisson summation
   (the Poisson summation step is analytic);
3. **named family payments**, one per cell piece (`PiecePaid`) and one for the centering
   (`CenteringPaid`), each derivable from per-cell saving shapes by the payment calculus
   (`piecePaid_of_powerSaving`, `piecePaid_of_logSaving`), the spectator reciprocal norm and the
   normalisation `𝒩_X I ≥ c·x`.

`Tail287_of_MinimalAnalyticProviders` — the conditional tail theorem with this provider set.
No provider mentions `R_Σ^P`, the tail statement, counterexamples or exact words.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

variable {ι : Type*}

/-! ### Packet components of `R_rel^main` -/

/-- The literal packet component `S_ξ = ∑_j ∑_d ℓ_X(d) Δ_{α_j}^{f_ξ,c_ξ}(d, b_{ξ,d})`. -/
noncomputable def Sxi (T : TensorSource ι) (ξ : ι) : ℝ :=
  ∑ j ∈ range T.ell, ∑ d ∈ T.D, T.lX d * DeltaRel T.S (T.α j) (T.f ξ) (T.c ξ) d (T.b ξ d)

/-- `R_rel^main = ∑_ξ Γ_ξ S_ξ`. -/
theorem RrelMain_eq_sum_Sxi (T : TensorSource ι) :
    T.RrelMain = ∑ ξ ∈ T.Xi, T.Γ ξ * Sxi T ξ := by
  unfold TensorSource.RrelMain Sxi
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [Finset.mul_sum]

/-! ### Cell pieces -/

/-- The eight named Ordering-B cell pieces. -/
inductive CellPiece
  | fabK1
  | fabKgt1
  | commonR
  | commonN
  | diagonal
  | nearDiag
  | zeroMode
  | sharp
  deriving DecidableEq, Repr

/-- All cell pieces. -/
def CellPiece.all : Finset CellPiece :=
  {.fabK1, .fabKgt1, .commonR, .commonN, .diagonal, .nearDiag, .zeroMode, .sharp}

/-- Per-packet Ordering-B cell data: literal `F_AB`, literal `F_AA` (with its sectors and
`F_AA^♯`), the centering term, the zero mode and the Cauchy factor `𝓑_ξ`. -/
structure OrderingBCells (S : TailSourceFamily ι) where
  fab : ℕ → ι → FABData
  faa : ℕ → ι → FAAData
  cent : ℕ → ι → ℝ
  zm : ℕ → ι → ℝ
  Bc : ℕ → ι → ℝ
  cent_nonneg : ∀ X ξ, 0 ≤ cent X ξ
  zm_nonneg : ∀ X ξ, 0 ≤ zm X ξ
  Bc_nonneg : ∀ X ξ, 0 ≤ Bc X ξ

namespace OrderingBCells

variable {S : TailSourceFamily ι} (C : OrderingBCells S)

/-- The value of each named cell piece. -/
noncomputable def piece (X : ℕ) (ξ : ι) : CellPiece → ℝ
  | .fabK1 => ‖(C.fab X ξ).FABpart (fun k => k = 1)‖
  | .fabKgt1 => ‖(C.fab X ξ).FABpart (fun k => k ≠ 1)‖
  | .commonR => ‖(C.faa X ξ).sector .commonR‖
  | .commonN => ‖(C.faa X ξ).sector .commonN‖
  | .diagonal => ‖(C.faa X ξ).sector .diagonal‖
  | .nearDiag => ‖(C.faa X ξ).sector .nearDiag‖
  | .zeroMode => C.zm X ξ
  | .sharp => ‖(C.faa X ξ).FAAsharp‖

theorem piece_nonneg (X : ℕ) (ξ : ι) (p : CellPiece) : 0 ≤ C.piece X ξ p := by
  cases p <;> simp only [piece] <;> first | exact norm_nonneg _ | exact C.zm_nonneg X ξ

end OrderingBCells

/-- **Ordering-B Poisson reduction** (source statement; `PAPER_VERIFIED_PARTIAL`): the
per-packet inequality obtained from the Type-II split (OB.1), the first Cauchy step with
`n₁ ≡ n₂ (fl)` retained (OB.2), the square expansion and Poisson summation, with the literal
`F_AB` (OB.7) and the literal `F_AA` (OB.9) split into its Opus-repair-2 sectors. -/
def OrderingBPoissonReduction (S : TailSourceFamily ι) (C : OrderingBCells S) : Prop :=
  ∀ X, ∀ ξ ∈ (S.T X).Xi, |Sxi (S.T X) ξ| ≤ C.cent X ξ + Real.sqrt (C.Bc X ξ *
    (‖(C.fab X ξ).FAB‖ + ‖(C.faa X ξ).sector .commonR‖ + ‖(C.faa X ξ).sector .commonN‖ +
      ‖(C.faa X ξ).sector .diagonal‖ + ‖(C.faa X ξ).sector .nearDiag‖ + C.zm X ξ +
      ‖(C.faa X ξ).FAAsharp‖))

/-- `√(∑ a_i) ≤ ∑ √a_i` for non-negative terms. -/
theorem sqrt_sum_le {κ : Type*} (s : Finset κ) (a : κ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    Real.sqrt (∑ i ∈ s, a i) ≤ ∑ i ∈ s, Real.sqrt (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hs : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    calc Real.sqrt (a j + ∑ i ∈ s, a i) ≤ Real.sqrt (a j) + Real.sqrt (∑ i ∈ s, a i) :=
          sqrt_add_le_sqrt_add_sqrt (ha j (Finset.mem_insert_self j s)) hs
      _ ≤ _ := by
          gcongr
          exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))

theorem sum_all (g : CellPiece → ℝ) :
    ∑ p ∈ CellPiece.all, g p = g .fabK1 + g .fabKgt1 + g .commonR + g .commonN +
      g .diagonal + g .nearDiag + g .zeroMode + g .sharp := by
  simp [CellPiece.all, Finset.sum_insert]
  ring

/-- **Per-packet cell bound**: `|S_ξ| ≤ cent_ξ + ∑_{pieces} √(𝓑_ξ · piece)`. -/
theorem cell_bound {S : TailSourceFamily ι} (C : OrderingBCells S)
    (hRed : OrderingBPoissonReduction S C) (X : ℕ) {ξ : ι} (hξ : ξ ∈ (S.T X).Xi) :
    |Sxi (S.T X) ξ| ≤ C.cent X ξ +
      ∑ p ∈ CellPiece.all, Real.sqrt (C.Bc X ξ * C.piece X ξ p) := by
  refine (hRed X ξ hξ).trans (add_le_add_right ?_ _)
  have hB := C.Bc_nonneg X ξ
  have hfab : ‖(C.fab X ξ).FAB‖ ≤ C.piece X ξ .fabK1 + C.piece X ξ .fabKgt1 := by
    simp only [OrderingBCells.piece]
    rw [(C.fab X ξ).FAB_split]; exact norm_add_le _ _
  calc Real.sqrt (C.Bc X ξ * (‖(C.fab X ξ).FAB‖ + ‖(C.faa X ξ).sector .commonR‖ +
        ‖(C.faa X ξ).sector .commonN‖ + ‖(C.faa X ξ).sector .diagonal‖ +
        ‖(C.faa X ξ).sector .nearDiag‖ + C.zm X ξ + ‖(C.faa X ξ).FAAsharp‖))
      ≤ Real.sqrt (∑ p ∈ CellPiece.all, C.Bc X ξ * C.piece X ξ p) := by
        apply Real.sqrt_le_sqrt
        rw [sum_all]
        simp only [OrderingBCells.piece]
        have := mul_le_mul_of_nonneg_left hfab hB
        simp only [OrderingBCells.piece] at this
        nlinarith [this]
    _ ≤ ∑ p ∈ CellPiece.all, Real.sqrt (C.Bc X ξ * C.piece X ξ p) :=
        sqrt_sum_le _ _ (fun p _ => mul_nonneg hB (C.piece_nonneg X ξ p))

/-! ### Family-level payments -/

/-- The family sum of one cell piece: `∑_ξ |Γ_ξ| √(𝓑_ξ · piece_ξ)`. -/
noncomputable def pieceSum {S : TailSourceFamily ι} (C : OrderingBCells S) (p : CellPiece)
    (X : ℕ) : ℝ :=
  ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| * Real.sqrt (C.Bc X ξ * C.piece X ξ p)

/-- The family centering sum `∑_ξ |Γ_ξ| cent_ξ`. -/
noncomputable def centSum {S : TailSourceFamily ι} (C : OrderingBCells S) (X : ℕ) : ℝ :=
  ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| * C.cent X ξ

/-- **Named payment of one cell piece.** -/
def PiecePaid (S : TailSourceFamily ι) (C : OrderingBCells S) (p : CellPiece) : Prop :=
  IsLittleOTarget (pieceSum C p) S.target

/-- **Named payment of the relative centering** (paid by RBDH through the family Cauchy). -/
def CenteringPaid (S : TailSourceFamily ι) (C : OrderingBCells S) : Prop :=
  IsLittleOTarget (centSum C) S.target

/-- **Named payment of the coprimality insertion.** -/
def CoprimalityPaid (S : TailSourceFamily ι) : Prop :=
  IsLittleOTarget (fun X => (S.T X).RrelCoprime) S.target

/-- **(REC.1) at family level.** -/
theorem RrelMain_bound {S : TailSourceFamily ι} (C : OrderingBCells S)
    (hRed : OrderingBPoissonReduction S C) (X : ℕ) :
    |(S.T X).RrelMain| ≤ centSum C X + ∑ p ∈ CellPiece.all, pieceSum C p X := by
  rw [RrelMain_eq_sum_Sxi]
  unfold centSum pieceSum
  rw [Finset.sum_comm (s := CellPiece.all)]
  calc |∑ ξ ∈ (S.T X).Xi, (S.T X).Γ ξ * Sxi (S.T X) ξ|
      ≤ ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ * Sxi (S.T X) ξ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ξ ∈ (S.T X).Xi, (|(S.T X).Γ ξ| * C.cent X ξ +
          ∑ p ∈ CellPiece.all, |(S.T X).Γ ξ| * Real.sqrt (C.Bc X ξ * C.piece X ξ p)) := by
        refine Finset.sum_le_sum (fun ξ hξ => ?_)
        rw [abs_mul, ← Finset.mul_sum, ← mul_add]
        exact mul_le_mul_of_nonneg_left (cell_bound C hRed X hξ) (abs_nonneg _)
    _ = _ := Finset.sum_add_distrib

/-- **`R_Σ^P = o(𝒩_X I)` from the minimal provider set** (kernel-proved implication). -/
theorem RSigmaP_littleO_of_minimal (S : TailSourceFamily ι) (C : OrderingBCells S)
    (hBase : BaseSWProvider S) (hCop : CoprimalityPaid S)
    (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
    (hP : ∀ p, PiecePaid S C p) :
    IsLittleOTarget (fun X => (S.T X).RSigmaP) S.target := by
  have hpieces : IsLittleOTarget (fun X => ∑ p ∈ CellPiece.all, |pieceSum C p X|) S.target :=
    IsLittleOTarget.sum_abs CellPiece.all (fun p => pieceSum C p) S.target_nonneg
      (fun p _ => hP p)
  have htot := ((hCent.abs.add hpieces).add hCop.abs).add (Rpaid_littleO S hBase).abs
  refine htot.of_le (fun X => ?_)
  rw [(S.T X).RSigmaP_eq_Rrel_add_Rpaid, (S.T X).Rrel_eq_main_sub_coprimality (S.compat X)]
  have h1 := RrelMain_bound C hRed X
  have hps : ∑ p ∈ CellPiece.all, pieceSum C p X ≤ ∑ p ∈ CellPiece.all, |pieceSum C p X| :=
    Finset.sum_le_sum (fun p _ => le_abs_self _)
  have hnn : 0 ≤ |centSum C X| + ∑ p ∈ CellPiece.all, |pieceSum C p X| +
      |(S.T X).RrelCoprime| + |(S.T X).Rpaid| := by positivity
  rw [abs_of_nonneg hnn]
  calc |(S.T X).RrelMain - (S.T X).RrelCoprime + (S.T X).Rpaid|
      ≤ |(S.T X).RrelMain| + |(S.T X).RrelCoprime| + |(S.T X).Rpaid| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by linarith [le_abs_self (centSum C X)]

/-- **Conditional tail theorem with the minimal provider set.**  Inputs: the seven-block
framework, the V99 base-layer provider, the coprimality payment, the Ordering-B Poisson
reduction, the centering payment and the eight named cell-piece payments.
NOT an unconditional result. -/
theorem Tail287_of_MinimalAnalyticProviders (S : TailSourceFamily ι) (C : OrderingBCells S)
    (Fw : SevenBlockTailFramework S) (hBase : BaseSWProvider S) (hCop : CoprimalityPaid S)
    (hRed : OrderingBPoissonReduction S C) (hCent : CenteringPaid S C)
    (hP : ∀ p, PiecePaid S C p) : Tail287Statement :=
  tail_of_remainder_littleO S Fw (RSigmaP_littleO_of_minimal S C hBase hCop hRed hCent hP)

end Erdos287.SourceChain
