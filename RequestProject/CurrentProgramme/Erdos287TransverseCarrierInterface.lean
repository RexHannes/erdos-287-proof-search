import Mathlib
import RequestProject.CurrentProgramme.Erdos287ReciprocalUnitaryFourier

/-!
# Transverse carrier interface — Erdős #287 (append-only)

The transverse mechanism available to this repository is *exactly* the finite reciprocal unitary
Fourier theorem of `Erdos287ReciprocalUnitaryFourier`, reused verbatim (no second proof).  What
is **not** available is the source-level input: the atomic carrier factorisation of `Q_*^red`,
the dependence of `B_*^red` on each carrier, and the existence of two simultaneously long usable
signless carriers.  Those are recorded here only as *unfilled* interface fields.

Explicitly **not** encoded anywhere in this repository:

* `E = e/a₁` and `R = r₂/c₂` are both long;
* `E · R > m L^K`;
* every transverse packet has a usable two-carrier pair;
* `THREEFACTOR-TRANSVERSE-SINGLECARRIER-RESIDUAL45` as an exact mathematical fact.

Contents.

* §1  `TransverseCarrierPacket`: a source interface with `Prop`-valued, **unfilled** fields;
* §2  the usability predicate, together with witnesses that it is neither automatic nor
  contradictory (so it can never be silently discharged);
* §3  the conditional transverse mechanism: *given* a usable pair of unit carriers and arbitrary
  `ℓ²` coefficients, the two-carrier reciprocal bound holds;
* §4  the research trichotomy as a bare datatype — no exhaustiveness theorem is stated or
  proved, since the literal source factorisation is not formalised.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseCarrier

open Erdos287.ReciprocalUnitaryFourier

/-! ## §1  The source interface -/

/-- Source interface for one transverse packet.

The three `Prop`-valued fields are **unfilled**: they are supplied by whoever instantiates the
packet, and nothing in this repository proves any of them for the physical source.  The numeric
fields carry no assumption beyond their types. -/
structure TransverseCarrierPacket where
  /-- The reduced modulus of the packet. -/
  modulus : ℕ
  /-- The (signed) reduced numerator. -/
  numerator : ℤ
  /-- The first candidate signless carrier. -/
  carrier1 : ℕ
  /-- The second candidate signless carrier. -/
  carrier2 : ℕ
  /-- The claimed atomic factorisation of the reduced modulus.  **Unfilled.** -/
  modulusFactorisation : Prop
  /-- The claimed unit conditions on both carriers.  **Unfilled.** -/
  carrierUnitConditions : Prop
  /-- The claimed normal form of the numerator in the two carriers.  **Unfilled.** -/
  numeratorNormalForm : Prop

/-! ## §2  Usability, and its non-automaticity -/

/-- A packet is *usable as a two-carrier pair* when all three source conditions hold.  This is a
hypothesis shell, never proved here. -/
def UsableTwoCarrierPair (P : TransverseCarrierPacket) : Prop :=
  P.modulusFactorisation ∧ P.carrierUnitConditions ∧ P.numeratorNormalForm

/-- **`usableTwoCarrierPair_not_automatic`.**  `LEAN_PROVED`.  There are packets which are not
usable: the existence of a usable two-carrier pair is a genuine, unproved condition. -/
theorem usableTwoCarrierPair_not_automatic :
    ∃ P : TransverseCarrierPacket, ¬ UsableTwoCarrierPair P := by
  refine ⟨⟨1, 0, 1, 1, False, True, True⟩, ?_⟩
  rintro ⟨h, -, -⟩
  exact h

/-- **`usableTwoCarrierPair_satisfiable`.**  `LEAN_PROVED`.  The shell is not contradictory
either.  Together with the previous theorem it is pinned down as a real, open condition. -/
theorem usableTwoCarrierPair_satisfiable :
    ∃ P : TransverseCarrierPacket, UsableTwoCarrierPair P :=
  ⟨⟨1, 0, 1, 1, True, True, True⟩, ⟨trivial, trivial, trivial⟩⟩

/-! ## §3  The conditional transverse mechanism -/

/-- **`transverseTwoCarrier_bound_of_unitSupport`.**  `LEAN_PROVED (CONDITIONAL)`.

*Given* two finite sets of unit carriers modulo `m` and a unit `Gamma`, the two-carrier
reciprocal bound holds for **arbitrary** `ℓ²` coefficients:

`‖∑_{S₁,S₂} α(S₁) β(S₂) e_m(Gamma S₁⁻¹ S₂⁻¹)‖² ≤ m ‖α‖₂² ‖β‖₂²`.

The hypotheses are exactly the unit conditions; nothing asserts that the physical transverse
source supplies them.  The pointwise formula of `Ω_H` (or of any other coefficient) is not
needed: only the `ℓ²` masses appear. -/
theorem transverseTwoCarrier_bound_of_unitSupport {m : ℕ} [NeZero m] {Gamma : ZMod m}
    (hGamma : IsUnit Gamma) (S₁ S₂ : Finset (ZMod m))
    (hS₁ : ∀ r ∈ S₁, IsUnit r) (hS₂ : ∀ s ∈ S₂, IsUnit s) (alpha beta : ZMod m → ℂ) :
    ‖∑ r ∈ S₁, ∑ s ∈ S₂, alpha r * beta s * ZMod.stdAddChar (Gamma * r⁻¹ * s⁻¹)‖ ^ 2
      ≤ (m : ℝ) * (∑ r ∈ S₁, ‖alpha r‖ ^ 2) * (∑ s ∈ S₂, ‖beta s‖ ^ 2) :=
  transverseTwoCarrierUnitaryFourier hGamma S₁ S₂ hS₁ hS₂ alpha beta

/-- **`transverseTwoCarrier_bound_with_fibre_weights`.**  `LEAN_PROVED (CONDITIONAL)`.  The same
bound in the form used by the research compiler, with explicit fibre multiplicities `M₁, M₂` and
energy bounds substituted on the right. -/
theorem transverseTwoCarrier_bound_with_fibre_weights {m : ℕ} [NeZero m] {Gamma : ZMod m}
    (hGamma : IsUnit Gamma) (S₁ S₂ : Finset (ZMod m))
    (hS₁ : ∀ r ∈ S₁, IsUnit r) (hS₂ : ∀ s ∈ S₂, IsUnit s) (alpha beta : ZMod m → ℂ)
    (M₁ M₂ E₁ E₂ : ℝ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hE₁ : ∑ r ∈ S₁, ‖alpha r‖ ^ 2 ≤ E₁) (hE₂ : ∑ s ∈ S₂, ‖beta s‖ ^ 2 ≤ E₂) :
    ‖∑ r ∈ S₁, ∑ s ∈ S₂, alpha r * beta s * ZMod.stdAddChar (Gamma * r⁻¹ * s⁻¹)‖ ^ 2
      ≤ (m : ℝ) * M₁ * M₂ * E₁ * E₂ := by
  have hE₁0 : (0 : ℝ) ≤ E₁ := le_trans (Finset.sum_nonneg fun r _ => by positivity) hE₁
  have hE₂0 : (0 : ℝ) ≤ E₂ := le_trans (Finset.sum_nonneg fun s _ => by positivity) hE₂
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  refine (transverseTwoCarrier_bound_of_unitSupport hGamma S₁ S₂ hS₁ hS₂ alpha beta).trans ?_
  calc (m : ℝ) * (∑ r ∈ S₁, ‖alpha r‖ ^ 2) * (∑ s ∈ S₂, ‖beta s‖ ^ 2)
      ≤ (m : ℝ) * E₁ * E₂ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hE₁ hm0) hE₂
          (Finset.sum_nonneg fun s _ => by positivity) (by positivity)
    _ ≤ (m : ℝ) * M₁ * M₂ * E₁ * E₂ := by
        have hbase : (0 : ℝ) ≤ (m : ℝ) * E₁ * E₂ := mul_nonneg (mul_nonneg hm0 hE₁0) hE₂0
        have hMM : (1 : ℝ) ≤ M₁ * M₂ := by nlinarith
        nlinarith [mul_nonneg hbase (sub_nonneg.mpr hMM)]

/-! ## §4  The research trichotomy (datatype only) -/

/-- The three research cases for the transverse conductor.  This is a bare datatype: **no**
exhaustiveness theorem is stated or proved, because the literal source factorisation of
`Q_*^red` has not been formalised. -/
inductive TransverseCarrierCase
  /-- Two usable long reciprocal carriers survive the reduced modulus. -/
  | twoCarrier
  /-- Only one usable long carrier survives. -/
  | singleCarrier
  /-- Conductor longness comes from a different source architecture. -/
  | otherCarrier
  deriving DecidableEq, Fintype, Repr

/-- **`transverseCarrierCase_no_exhaustiveness_claimed`.**  `LEAN_PROVED`.  The datatype records
three labels and nothing else: the three cases are pairwise distinct, and no packet is assigned
to any of them by this repository. -/
theorem transverseCarrierCase_no_exhaustiveness_claimed :
    TransverseCarrierCase.twoCarrier ≠ TransverseCarrierCase.singleCarrier ∧
    TransverseCarrierCase.twoCarrier ≠ TransverseCarrierCase.otherCarrier ∧
    TransverseCarrierCase.singleCarrier ≠ TransverseCarrierCase.otherCarrier := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end TransverseCarrier
end Erdos287
