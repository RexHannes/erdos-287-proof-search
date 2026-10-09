import RequestProject.Erdos287.CurrentTail.AuxiliaryErrors

/-!
# Erdős #287 — current tail consolidation: literal remainder recombination

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The conditional implication

  **all listed analytic providers + the Ordering-B source dictionary ⟹ `R_Σ^P(X) = o(𝒩_X I)`**

is kernel-proved here (`RSigmaP_littleO_of_providers`).

Inputs, each named and separate:

* analytic providers (never constructed): `MaynardE1Estimate`, `PascadiE2Printed`,
  `QuantitativeTH`, `BDHFamily` (ordinary BDH), `SpectatorMomentFamily` (reciprocal divisor
  moment), `BaseSWProvider` (tiny-modulus SW + size), `AuxPieceProviders` (the auxiliary
  pieces of the ledger);
* the **source dictionary** `OrderingBSourceDictionary` (status `Candidate`,
  UNFORMALISED_SOURCE): the Ordering-B Maynard reduction bounding `R_rel^main` by the ledger
  pieces and linking each analytic provider to its piece.  It is *not* an analytic provider and
  is never hidden inside one.

No provider conclusion mentions `RSigmaP`; the audit checks this at build time.

Exact (kernel) ingredients used: `RSigmaP_eq_Rrel_add_Rpaid` (V99),
`Rrel_eq_main_sub_coprimality` (coprimality insertion), `Rpaid_bound` (base payment) and the
finite little-`o` calculus `IsLittleOTarget.*`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.CurrentTail

/-- `g = o(target)` along `X → ∞` (with an explicit `ε`–`X₀` quantifier). -/
def IsLittleOTarget (g target : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X0 : ℕ, ∀ X ≥ X0, |g X| ≤ ε * target X

namespace IsLittleOTarget

variable {g h target : ℕ → ℝ}

theorem of_le (hg : IsLittleOTarget g target) {f : ℕ → ℝ} (hle : ∀ X, |f X| ≤ |g X|) :
    IsLittleOTarget f target := by
  intro ε hε
  obtain ⟨X0, hX0⟩ := hg ε hε
  exact ⟨X0, fun X hX => (hle X).trans (hX0 X hX)⟩

theorem abs (hg : IsLittleOTarget g target) : IsLittleOTarget (fun X => |g X|) target :=
  hg.of_le (fun X => by rw [abs_abs])

theorem add (hg : IsLittleOTarget g target) (hh : IsLittleOTarget h target) :
    IsLittleOTarget (fun X => g X + h X) target := by
  intro ε hε
  obtain ⟨X1, h1⟩ := hg (ε / 2) (by linarith)
  obtain ⟨X2, h2⟩ := hh (ε / 2) (by linarith)
  refine ⟨max X1 X2, fun X hX => ?_⟩
  have a1 := h1 X (le_trans (le_max_left _ _) hX)
  have a2 := h2 X (le_trans (le_max_right _ _) hX)
  calc |g X + h X| ≤ |g X| + |h X| := abs_add_le _ _
    _ ≤ ε / 2 * target X + ε / 2 * target X := add_le_add a1 a2
    _ = ε * target X := by ring

theorem zero (htarget : ∀ X, 0 ≤ target X) : IsLittleOTarget (fun _ => 0) target :=
  fun ε hε => ⟨0, fun X _ => by simpa using mul_nonneg hε.le (htarget X)⟩

theorem sum_abs {κ : Type*} [DecidableEq κ] (s : Finset κ) (G : κ → ℕ → ℝ)
    (htarget : ∀ X, 0 ≤ target X) (hs : ∀ k ∈ s, IsLittleOTarget (G k) target) :
    IsLittleOTarget (fun X => ∑ k ∈ s, |G k X|) target := by
  induction s using Finset.induction_on with
  | empty => simpa using zero htarget
  | insert a s ha ih =>
    have h1 : IsLittleOTarget (fun X => |G a X| + ∑ k ∈ s, |G k X|) target :=
      (hs a (Finset.mem_insert_self a s)).abs.add
        (ih (fun k hk => hs k (Finset.mem_insert_of_mem hk)))
    exact h1.of_le (fun X => by rw [Finset.sum_insert ha])

end IsLittleOTarget

/-- A family of literal tensor sources indexed by the scale `X`, with the normalisation
`𝒩_X I` and the ledger pieces. -/
structure TailSourceFamily (ι : Type*) where
  T : ℕ → TensorSource ι
  target : ℕ → ℝ
  target_nonneg : ∀ X, 0 ≤ target X
  compat : ∀ X, ∀ ξ ∈ (T X).Xi, ∀ d ∈ (T X).D, (T X).b ξ d ≡ (T X).c ξ [MOD (T X).f ξ]
  piece : AuxError → ℕ → ℝ

variable {ι : Type*}

/-- **Ordinary BDH family (external analytic provider).** -/
def BDHFamily (S : TailSourceFamily ι) (Q0 Q : ℕ → ℕ) (B : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ X f : ℕ, 0 < f → BDHStatement (S.T X).S (fun q => Nat.Coprime f q) (Q0 X) (Q X) (B X)

/-- **Reciprocal divisor moment family (external analytic provider).** -/
def SpectatorMomentFamily (E : ℕ) (Xmax : ℕ → ℕ) (Cm : ℕ → ℝ) : Prop :=
  ∀ X, ReciprocalDivisorMoment E (Xmax X) (Cm X)

/-- **Tiny-modulus Siegel–Walfisz input with size comparison (external analytic provider).** -/
def BaseSWProvider (S : TailSourceFamily ι) : Prop :=
  ∃ η L : ℕ → ℝ,
    (∀ X, ∀ j ∈ range (S.T X).ell, ∀ ξ ∈ (S.T X).Xi,
      |progErr (S.T X).S ((S.T X).α j) ((S.T X).mass j) ((S.T X).f ξ) ((S.T X).c ξ)| ≤ η X) ∧
    (∀ X, |∑ d ∈ (S.T X).D, (S.T X).lX d / (Nat.totient d : ℝ)| ≤ L X) ∧
    IsLittleOTarget (fun X => (S.T X).ell * (∑ ξ ∈ (S.T X).Xi, |(S.T X).Γ ξ|) * η X * L X)
      S.target

/-- **Auxiliary piece providers (external).** -/
def AuxPieceProviders (S : TailSourceFamily ι) : Prop :=
  ∀ e ∈ auxPieces, IsLittleOTarget (S.piece e) S.target

/-- **Ordering-B source dictionary (UNFORMALISED_SOURCE; status `Candidate`).**  The
Maynard-reduction bookkeeping of the relative main part and the coprimality error, and the
links from each analytic provider to its ledger piece.  Separate from all providers. -/
structure OrderingBSourceDictionary (S : TailSourceFamily ι) (E1 E2p E2q BDH Mom : Prop) :
    Prop where
  main : ∀ X, |(S.T X).RrelMain| ≤ ∑ e ∈ mainPieces, |S.piece e X|
  coprime : ∀ X, |(S.T X).RrelCoprime| ≤ |S.piece .coprimality X|
  e1_link : E1 → IsLittleOTarget (S.piece .e1Bilinear) S.target
  e2_link : E2p → E2q → IsLittleOTarget (S.piece .e2Spectral) S.target
  rbdh_link : BDH → Mom → IsLittleOTarget (S.piece .rbdhFamily) S.target

/-- The already-paid term is `o(target)` from the base SW provider (kernel, via `Rpaid_bound`). -/
theorem Rpaid_littleO (S : TailSourceFamily ι) (h : BaseSWProvider S) :
    IsLittleOTarget (fun X => (S.T X).Rpaid) S.target := by
  obtain ⟨η, L, hη, hL, ho⟩ := h
  refine ho.of_le (fun X => ?_)
  exact ((S.T X).Rpaid_bound (hη X) (hL X)).trans (le_abs_self _)

/-- **Literal remainder recombination (conditional, kernel-proved).**
All listed analytic providers + the Ordering-B source dictionary ⟹ `R_Σ^P = o(𝒩_X I)`. -/
theorem RSigmaP_littleO_of_providers (S : TailSourceFamily ι)
    {θ σlo σhi δ A0 A θQ θR θH δ2 : ℝ} {B E : ℕ} {Q0 Q Xmax : ℕ → ℕ}
    {Bf : ℕ → ℝ → ℝ → ℝ} {Cm : ℕ → ℝ}
    (D : OrderingBSourceDictionary S (MaynardE1Estimate θ σlo σhi δ B A0 A)
      (PascadiE2Printed θQ θR θH δ2) (QuantitativeTH θQ θR θH δ2) (BDHFamily S Q0 Q Bf)
      (SpectatorMomentFamily E Xmax Cm))
    (hE1 : MaynardE1Estimate θ σlo σhi δ B A0 A)
    (hE2p : PascadiE2Printed θQ θR θH δ2) (hE2q : QuantitativeTH θQ θR θH δ2)
    (hBDH : BDHFamily S Q0 Q Bf) (hMom : SpectatorMomentFamily E Xmax Cm)
    (hBase : BaseSWProvider S) (hAux : AuxPieceProviders S) :
    IsLittleOTarget (fun X => (S.T X).RSigmaP) S.target := by
  have hmain : ∀ e ∈ mainPieces, IsLittleOTarget (S.piece e) S.target := by
    intro e he
    have aux : ∀ e', e' ∈ auxPieces → IsLittleOTarget (S.piece e') S.target := hAux
    simp only [mainPieces, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact aux _ (by decide)
    · exact aux _ (by decide)
    · exact aux _ (by decide)
    · exact aux _ (by decide)
    · exact aux _ (by decide)
    · exact aux _ (by decide)
    · exact D.rbdh_link hBDH hMom
    · exact D.e1_link hE1
    · exact D.e2_link hE2p hE2q
  have hsum := IsLittleOTarget.sum_abs mainPieces S.piece S.target_nonneg hmain
  have hcop : IsLittleOTarget (S.piece .coprimality) S.target := hAux _ (by decide)
  have hpaid := Rpaid_littleO S hBase
  have htot := (hsum.add hcop.abs).add hpaid.abs
  refine htot.of_le (fun X => ?_)
  rw [(S.T X).RSigmaP_eq_Rrel_add_Rpaid, (S.T X).Rrel_eq_main_sub_coprimality (S.compat X)]
  have h1 := D.main X
  have h2 := D.coprime X
  have hnn : 0 ≤ ∑ e ∈ mainPieces, |S.piece e X| + |S.piece .coprimality X| +
      |(S.T X).Rpaid| := by positivity
  rw [abs_of_nonneg hnn]
  calc |(S.T X).RrelMain - (S.T X).RrelCoprime + (S.T X).Rpaid|
      ≤ |(S.T X).RrelMain| + |(S.T X).RrelCoprime| + |(S.T X).Rpaid| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by gcongr

end Erdos287.CurrentTail
