import RequestProject.Erdos287.SourceChain.MinimalTail

/-!
# Erdős #287 — source chain: the payment calculus (per-cell savings ⟹ family payments)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Kernel-proved conversions from *per-cell* saving shapes to the *family* payments used by
`Tail287_of_MinimalAnalyticProviders`, with the packet family paid through the reciprocal
density (no logarithmic error is ever multiplied by a raw packet count):

* `FamilyScale` — the scale `x_X → ∞` and the normalisation `𝒩_X I ≥ c·x_X` (source facts);
* `SpectatorReciprocalNorm` — (OB.4) `∑_ξ |Γ_ξ|/f_ξ ≤ (log x)^{C_D}` (`EXTERNAL_ANALYTIC`);
* `pieceSum_le_of_cell` — `√(𝓑_ξ piece_ξ) ≤ (x/f_ξ) s(X)` for all `ξ` gives
  `∑_ξ |Γ_ξ| √(𝓑_ξ piece_ξ) ≤ x · s(X) · ∑_ξ |Γ_ξ|/f_ξ`;
* `piecePaid_of_powerSaving` — a fixed power saving `x^{-κ}` (times any log power) pays;
* `piecePaid_of_logSaving` — an arbitrary log saving `(log x)^{-A}` (every `A`) pays;
* `centeringPaid_of_RBDH` — (OB.3): the centering source shape
  `cent_ξ ≤ M √(R(f_ξ)/φ(f_ξ))`, the fibre multiplicity `∑_{f_ξ = F} |Γ_ξ| ≤ τ(F)^C`, the
  spectator norm in `φ`-form and an RBDH bound `∑_F τ(F)^C R(F) ≤ C_A N² (log x)^{-A}`
  (every `A`) with `MN ≤ K x` give `CenteringPaid`.
-/

open scoped BigOperators
open Finset Filter

namespace Erdos287.SourceChain

open Erdos287.CurrentTail

variable {ι : Type*}

/-- Scale and normalisation of the source family. -/
structure FamilyScale (S : TailSourceFamily ι) where
  x : ℕ → ℝ
  x_large : ∀ B : ℝ, ∃ X0 : ℕ, ∀ X ≥ X0, B ≤ x X
  c : ℝ
  c_pos : 0 < c
  target_ge : ∀ X, c * x X ≤ S.target X

/-- **(OB.4) spectator reciprocal-density norm** (`EXTERNAL_ANALYTIC`). -/
def SpectatorReciprocalNorm (S : TailSourceFamily ι) (Fs : FamilyScale S) (CD : ℝ) : Prop :=
  ∀ X, ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| / ((S.T X).f ξ : ℝ) ≤ Real.log (Fs.x X) ^ CD

/-- Per-cell fixed power saving for one piece. -/
def PowerSavingCell (S : TailSourceFamily ι) (C : OrderingBCells S) (Fs : FamilyScale S)
    (p : CellPiece) : Prop :=
  ∃ K κ Cc : ℝ, 0 < κ ∧ 0 ≤ Cc ∧ ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
    Real.sqrt (C.Bc X ξ * C.piece X ξ p) ≤
      Fs.x X / ((S.T X).f ξ : ℝ) * (Cc * Real.log (Fs.x X) ^ K * Fs.x X ^ (-κ))

/-- Per-cell arbitrary logarithmic saving for one piece. -/
def LogSavingCell (S : TailSourceFamily ι) (C : OrderingBCells S) (Fs : FamilyScale S)
    (p : CellPiece) : Prop :=
  ∀ A : ℝ, ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ X1 : ℕ, ∀ X ≥ X1, ∀ ξ ∈ (S.T X).Xi,
    Real.sqrt (C.Bc X ξ * C.piece X ξ p) ≤
      Fs.x X / ((S.T X).f ξ : ℝ) * (Cc * Real.log (Fs.x X) ^ (-A))

theorem FamilyScale.eventually {S : TailSourceFamily ι} (Fs : FamilyScale S) {P : ℝ → Prop}
    (h : ∀ᶠ y in atTop, P y) : ∃ X0 : ℕ, ∀ X ≥ X0, P (Fs.x X) := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 h
  obtain ⟨X0, hX0⟩ := Fs.x_large B
  exact ⟨X0, fun X hX => hB _ (hX0 X hX)⟩

/-- Per-cell bound ⟹ family bound through the reciprocal density. -/
theorem pieceSum_le_of_cell {S : TailSourceFamily ι} (C : OrderingBCells S) (p : CellPiece)
    (x s : ℕ → ℝ) (X : ℕ)
    (h : ∀ ξ ∈ (S.T X).Xi, Real.sqrt (C.Bc X ξ * C.piece X ξ p) ≤
      x X / ((S.T X).f ξ : ℝ) * s X) :
    pieceSum C p X ≤ x X * s X * ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| / ((S.T X).f ξ : ℝ) := by
  unfold pieceSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ξ hξ => ?_)
  calc |(S.T X).Γ ξ| * Real.sqrt (C.Bc X ξ * C.piece X ξ p)
      ≤ |(S.T X).Γ ξ| * (x X / ((S.T X).f ξ : ℝ) * s X) :=
        mul_le_mul_of_nonneg_left (h ξ hξ) (abs_nonneg _)
    _ = x X * s X * (|(S.T X).Γ ξ| / ((S.T X).f ξ : ℝ)) := by ring

theorem pieceSum_nonneg {S : TailSourceFamily ι} (C : OrderingBCells S) (p : CellPiece)
    (X : ℕ) : 0 ≤ pieceSum C p X :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

/-- Generic: `0 ≤ g X ≤ x_X · e(X)` with `e(X) → 0` (along `x`) gives `g = o(𝒩_X I)`. -/
theorem littleO_of_scale {S : TailSourceFamily ι} (Fs : FamilyScale S) (g e : ℕ → ℝ)
    (hg0 : ∀ X, 0 ≤ g X) (hge : ∃ X1 : ℕ, ∀ X ≥ X1, g X ≤ Fs.x X * e X)
    (he : ∀ δ : ℝ, 0 < δ → ∃ X0 : ℕ, ∀ X ≥ X0, e X ≤ δ) :
    IsLittleOTarget g S.target := by
  intro ε hε
  obtain ⟨X1, hX1⟩ := hge
  obtain ⟨X0, hX0⟩ := he (ε * Fs.c) (mul_pos hε Fs.c_pos)
  obtain ⟨X2, hX2⟩ := Fs.x_large 0
  refine ⟨max (max X0 X1) X2, fun X hX => ?_⟩
  have h0 := hX0 X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
  have h1 := hX1 X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
  have h2 := hX2 X (le_trans (le_max_right _ _) hX)
  rw [abs_of_nonneg (hg0 X)]
  calc g X ≤ Fs.x X * e X := h1
    _ ≤ Fs.x X * (ε * Fs.c) := mul_le_mul_of_nonneg_left h0 h2
    _ = ε * (Fs.c * Fs.x X) := by ring
    _ ≤ ε * S.target X := mul_le_mul_of_nonneg_left (Fs.target_ge X) hε.le

/-- `C (log y)^K y^{-κ} (log y)^{C_D} → 0`. -/
theorem power_log_small {Cc K κ CD : ℝ} (hκ : 0 < κ) (hCc : 0 ≤ Cc) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ y in atTop,
      Cc * Real.log y ^ K * y ^ (-κ) * Real.log y ^ CD ≤ δ := by
  intro δ hδ
  obtain ⟨Y0, hY0⟩ := logCost_absorbed (by linarith : (0 : ℝ) < κ / 2) (K + CD)
  have h1 : ∀ᶠ y in atTop, Real.log y ^ (K + CD) ≤ y ^ (κ / 2) :=
    Filter.eventually_atTop.2 ⟨Y0, hY0⟩
  have h2 : ∀ᶠ y in atTop, y ^ (-(κ / 2)) < δ / (Cc + 1) :=
    (tendsto_order.1 (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < κ / 2))).2 _
      (by positivity)
  have h3 : ∀ᶠ y in atTop, (1 : ℝ) < y := Filter.eventually_gt_atTop 1
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  have hy0 : 0 < y := by linarith
  have hL : 0 < Real.log y := Real.log_pos hy3
  have e1 : Real.log y ^ K * Real.log y ^ CD = Real.log y ^ (K + CD) :=
    (Real.rpow_add hL K CD).symm
  have e2 : y ^ (κ / 2) * y ^ (-κ) = y ^ (-(κ / 2)) := by
    rw [← Real.rpow_add hy0]; ring_nf
  calc Cc * Real.log y ^ K * y ^ (-κ) * Real.log y ^ CD
      = Cc * (Real.log y ^ (K + CD)) * y ^ (-κ) := by rw [← e1]; ring
    _ ≤ Cc * y ^ (κ / 2) * y ^ (-κ) := by gcongr
    _ = Cc * y ^ (-(κ / 2)) := by rw [mul_assoc, e2]
    _ ≤ Cc * (δ / (Cc + 1)) := mul_le_mul_of_nonneg_left hy2.le hCc
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith

/-- **Power saving pays.** -/
theorem piecePaid_of_powerSaving {S : TailSourceFamily ι} (C : OrderingBCells S)
    (Fs : FamilyScale S) {CD : ℝ} (hspec : SpectatorReciprocalNorm S Fs CD) (p : CellPiece)
    (h : PowerSavingCell S C Fs p) : PiecePaid S C p := by
  obtain ⟨K, κ, Cc, hκ, hCc, X1, hcell⟩ := h
  set e : ℕ → ℝ := fun X => Cc * Real.log (Fs.x X) ^ K * Fs.x X ^ (-κ) *
    Real.log (Fs.x X) ^ CD
  obtain ⟨X2, hX2⟩ := Fs.x_large 1
  refine littleO_of_scale Fs (pieceSum C p) e (pieceSum_nonneg C p)
    ⟨max X1 X2, fun X hX => ?_⟩ ?_
  · have hle := pieceSum_le_of_cell C p Fs.x
      (fun X => Cc * Real.log (Fs.x X) ^ K * Fs.x X ^ (-κ)) X
      (hcell X (le_trans (le_max_left _ _) hX))
    have hx := hX2 X (le_trans (le_max_right _ _) hX)
    have hs0 : 0 ≤ Cc * Real.log (Fs.x X) ^ K * Fs.x X ^ (-κ) := by
      have : 0 ≤ Real.log (Fs.x X) := Real.log_nonneg hx
      positivity
    calc pieceSum C p X ≤ _ := hle
      _ ≤ Fs.x X * (Cc * Real.log (Fs.x X) ^ K * Fs.x X ^ (-κ)) *
            Real.log (Fs.x X) ^ CD :=
          mul_le_mul_of_nonneg_left (hspec X) (mul_nonneg (by linarith) hs0)
      _ = Fs.x X * e X := by simp only [e]; ring
  · intro δ hδ
    exact Fs.eventually (power_log_small hκ hCc δ hδ)

/-- `C (log y)^{-(C_D+1)} (log y)^{C_D} → 0`. -/
theorem log_saving_small {Cc CD : ℝ} :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ y in atTop,
      Cc * Real.log y ^ (-(CD + 1)) * Real.log y ^ CD ≤ δ := by
  intro δ hδ
  have h1 : ∀ᶠ y in atTop, (Cc + 1) / δ ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have h3 : ∀ᶠ y in atTop, (1 : ℝ) < y := Filter.eventually_gt_atTop 1
  filter_upwards [h1, h3] with y hy1 hy3
  have hL : 0 < Real.log y := Real.log_pos hy3
  have e1 : Real.log y ^ (-(CD + 1)) * Real.log y ^ CD = (Real.log y)⁻¹ := by
    rw [← Real.rpow_add hL]; ring_nf; exact Real.rpow_neg_one _
  rw [mul_assoc, e1, ← div_eq_mul_inv, div_le_iff₀ hL]
  rw [div_le_iff₀ hδ] at hy1
  nlinarith

/-- **Arbitrary log saving pays.** -/
theorem piecePaid_of_logSaving {S : TailSourceFamily ι} (C : OrderingBCells S)
    (Fs : FamilyScale S) {CD : ℝ} (hspec : SpectatorReciprocalNorm S Fs CD) (p : CellPiece)
    (h : LogSavingCell S C Fs p) : PiecePaid S C p := by
  obtain ⟨Cc, hCc, X1, hcell⟩ := h (CD + 1)
  set e : ℕ → ℝ := fun X => Cc * Real.log (Fs.x X) ^ (-(CD + 1)) * Real.log (Fs.x X) ^ CD
  obtain ⟨X2, hX2⟩ := Fs.x_large 1
  refine littleO_of_scale Fs (pieceSum C p) e (pieceSum_nonneg C p)
    ⟨max X1 X2, fun X hX => ?_⟩ ?_
  · have hle := pieceSum_le_of_cell C p Fs.x
      (fun X => Cc * Real.log (Fs.x X) ^ (-(CD + 1))) X
      (hcell X (le_trans (le_max_left _ _) hX))
    have hx := hX2 X (le_trans (le_max_right _ _) hX)
    have hs0 : 0 ≤ Cc * Real.log (Fs.x X) ^ (-(CD + 1)) := by
      have : 0 ≤ Real.log (Fs.x X) := Real.log_nonneg hx
      positivity
    calc pieceSum C p X ≤ _ := hle
      _ ≤ Fs.x X * (Cc * Real.log (Fs.x X) ^ (-(CD + 1))) * Real.log (Fs.x X) ^ CD :=
          mul_le_mul_of_nonneg_left (hspec X) (mul_nonneg (by linarith) hs0)
      _ = Fs.x X * e X := by simp only [e]; ring
  · intro δ hδ
    exact Fs.eventually (log_saving_small δ hδ)

/-! ### Centering through RBDH (OB.3) -/

/-- **Centering source shape** (V100R relative `E₃` centering, `PAPER_VERIFIED_PARTIAL`):
`cent_ξ ≤ M_X √(R_X(f_ξ)/φ(f_ξ))` with `R_X ≥ 0`, together with the fibre multiplicity
`∑_{f_ξ = F} |Γ_ξ| ≤ τ(F)^{Cτ}`. -/
structure CenteringSource (S : TailSourceFamily ι) (C : OrderingBCells S) (Cτ : ℕ) where
  Mx : ℕ → ℝ
  Nx : ℕ → ℝ
  R : ℕ → ℕ → ℝ
  Mx_nonneg : ∀ X, 0 ≤ Mx X
  Nx_nonneg : ∀ X, 0 ≤ Nx X
  R_nonneg : ∀ X F, 0 ≤ R X F
  cent_le : ∀ X, ∀ ξ ∈ (S.T X).Xi,
    C.cent X ξ ≤ Mx X * Real.sqrt (R X ((S.T X).f ξ) / (Nat.totient ((S.T X).f ξ) : ℝ))
  fibre : ∀ X, ∀ F ∈ (S.T X).Xi.image (S.T X).f,
    ∑ ξ ∈ (S.T X).Xi.filter (fun ξ => (S.T X).f ξ = F), |(S.T X).Γ ξ| ≤ (tau F : ℝ) ^ Cτ

/-- **Centering is paid** by: the spectator norm in `φ`-form, the RBDH family bound (every
`A`) and the size relation `M N ≤ K x`. -/
theorem centeringPaid_of_RBDH {S : TailSourceFamily ι} (C : OrderingBCells S)
    (Fs : FamilyScale S) {Cτ : ℕ} (Src : CenteringSource S C Cτ) {CD K0 : ℝ}
    (hspecφ : ∀ X, ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| / (Nat.totient ((S.T X).f ξ) : ℝ) ≤
      Real.log (Fs.x X) ^ CD)
    (hRBDH : ∀ A : ℝ, ∃ CA : ℝ, 0 ≤ CA ∧ ∀ X,
      ∑ F ∈ (S.T X).Xi.image (S.T X).f, (tau F : ℝ) ^ Cτ * Src.R X F ≤
        CA * Src.Nx X ^ 2 * Real.log (Fs.x X) ^ (-A))
    (hsize : ∀ X, Src.Mx X * Src.Nx X ≤ K0 * Fs.x X) :
    CenteringPaid S C := by
  obtain ⟨CA, hCA, hR⟩ := hRBDH (CD + 2)
  set e : ℕ → ℝ := fun X => K0 * Real.sqrt CA * (Real.log (Fs.x X))⁻¹
  obtain ⟨X2, hX2⟩ := Fs.x_large (Real.exp 1)
  have hcent0 : ∀ X, 0 ≤ centSum C X := fun X =>
    Finset.sum_nonneg (fun ξ _ => mul_nonneg (abs_nonneg _) (C.cent_nonneg X ξ))
  refine littleO_of_scale Fs (centSum C) e hcent0 ⟨X2, fun X hX => ?_⟩ ?_
  · have hx := hX2 X hX
    have hxpos : 0 < Fs.x X := lt_of_lt_of_le (Real.exp_pos 1) hx
    have hL1 : 1 ≤ Real.log (Fs.x X) := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
    have hL : 0 < Real.log (Fs.x X) := by linarith
    have hpos : ∀ ξ ∈ (S.T X).Xi, 0 < (S.T X).f ξ := (S.T X).f_pos
    -- family Cauchy (OB.3)
    have hfam : centSum C X ≤ Src.Mx X *
        Real.sqrt (∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| / (Nat.totient ((S.T X).f ξ) : ℝ)) *
        Real.sqrt (∑ F ∈ (S.T X).Xi.image (S.T X).f, (tau F : ℝ) ^ Cτ * Src.R X F) := by
      classical
      have key := family_payment_tau ((S.T X).Xi.attach) (fun ξ => (S.T X).f ξ.1)
        (fun ξ => (S.T X).Γ ξ.1) (fun ξ => hpos ξ.1 ξ.2) (Src.R X) (Src.R_nonneg X)
        (Src.Mx_nonneg X) (C := Cτ) (by
          intro F hF
          have hF' : F ∈ (S.T X).Xi.image (S.T X).f := by
            obtain ⟨ξ, -, rfl⟩ := Finset.mem_image.1 hF
            exact Finset.mem_image_of_mem _ ξ.2
          refine le_trans (le_of_eq ?_) (Src.fibre X F hF')
          rw [Finset.sum_filter, Finset.sum_filter]
          exact Finset.sum_attach (S.T X).Xi
            (fun ξ => if (S.T X).f ξ = F then |(S.T X).Γ ξ| else 0))
      have himg : (S.T X).Xi.attach.image (fun ξ => (S.T X).f ξ.1) =
          (S.T X).Xi.image (S.T X).f := by
        ext F; simp [Finset.mem_image]
      rw [himg, Finset.sum_attach (S.T X).Xi
        (fun ξ => |(S.T X).Γ ξ| / (Nat.totient ((S.T X).f ξ) : ℝ))] at key
      rw [Finset.sum_attach (S.T X).Xi (fun ξ => |(S.T X).Γ ξ| * Src.Mx X *
        Real.sqrt (Src.R X ((S.T X).f ξ) / (Nat.totient ((S.T X).f ξ) : ℝ)))] at key
      refine le_trans ?_ key
      unfold centSum
      refine Finset.sum_le_sum (fun ξ hξ => ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Src.cent_le X ξ hξ) (abs_nonneg _)
    have ha := hspecφ X
    have hb := hR X
    set a := ∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ| / (Nat.totient ((S.T X).f ξ) : ℝ)
    set b := ∑ F ∈ (S.T X).Xi.image (S.T X).f, (tau F : ℝ) ^ Cτ * Src.R X F
    have ha0 : 0 ≤ a := Finset.sum_nonneg (fun _ _ => by positivity)
    have hb0 : 0 ≤ b := Finset.sum_nonneg (fun F _ => mul_nonneg (by positivity)
      (Src.R_nonneg X F))
    have hab : a * b ≤ CA * Src.Nx X ^ 2 * (Real.log (Fs.x X))⁻¹ ^ 2 := by
      have hLCD : 0 ≤ Real.log (Fs.x X) ^ CD := Real.rpow_nonneg hL.le _
      calc a * b ≤ Real.log (Fs.x X) ^ CD *
            (CA * Src.Nx X ^ 2 * Real.log (Fs.x X) ^ (-(CD + 2))) :=
            mul_le_mul ha hb hb0 hLCD
        _ = CA * Src.Nx X ^ 2 * (Real.log (Fs.x X) ^ CD *
              Real.log (Fs.x X) ^ (-(CD + 2))) := by ring
        _ = CA * Src.Nx X ^ 2 * (Real.log (Fs.x X))⁻¹ ^ 2 := by
            rw [← Real.rpow_add hL, show CD + -(CD + 2) = -(2 : ℝ) by ring,
              Real.rpow_neg hL.le, Real.rpow_two, inv_pow]
    calc centSum C X ≤ Src.Mx X * Real.sqrt a * Real.sqrt b := hfam
      _ = Real.sqrt (Src.Mx X ^ 2 * (a * b)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Src.Mx_nonneg X),
            Real.sqrt_mul ha0]; ring
      _ ≤ Real.sqrt (Src.Mx X ^ 2 * (CA * Src.Nx X ^ 2 * (Real.log (Fs.x X))⁻¹ ^ 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hab (sq_nonneg _))
      _ = Src.Mx X * Src.Nx X * Real.sqrt CA * (Real.log (Fs.x X))⁻¹ := by
          rw [show Src.Mx X ^ 2 * (CA * Src.Nx X ^ 2 * (Real.log (Fs.x X))⁻¹ ^ 2) =
            (Src.Mx X * Src.Nx X * (Real.log (Fs.x X))⁻¹) ^ 2 * CA by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by
              have := Src.Mx_nonneg X; have := Src.Nx_nonneg X; positivity)]
          ring
      _ ≤ K0 * Fs.x X * Real.sqrt CA * (Real.log (Fs.x X))⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsize X) (Real.sqrt_nonneg _))
            (inv_nonneg.2 hL.le)
      _ = Fs.x X * e X := by simp only [e]; ring
  · intro δ hδ
    refine Fs.eventually (P := fun y => K0 * Real.sqrt CA * (Real.log y)⁻¹ ≤ δ) ?_
    have h1 : ∀ᶠ y in atTop, (K0 * Real.sqrt CA + 1) / δ ≤ Real.log y :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    have h3 : ∀ᶠ y in atTop, (1 : ℝ) < y := Filter.eventually_gt_atTop 1
    filter_upwards [h1, h3] with y hy1 hy3
    have hL : 0 < Real.log y := Real.log_pos hy3
    rw [← div_eq_mul_inv, div_le_iff₀ hL]
    rw [div_le_iff₀ hδ] at hy1
    nlinarith [Real.sqrt_nonneg CA]

end Erdos287.SourceChain
