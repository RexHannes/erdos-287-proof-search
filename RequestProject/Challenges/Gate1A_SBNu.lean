import Mathlib
import RequestProject.TrustedBank.Interfaces.ZeroSetTransport

/-!
# Challenge A — Gate 1A, the SB-ν fibre bound  (**OPEN**)

Controlling line: *for every fixed nonzero `ν` in the source range, the synchronized
two-view fibre count `N_ν` must be `X^{o(1)}`.*

**Status: OPEN.**  Nothing in this file is asserted as proved, and nothing here is
imported by `TrustedBank/`.

### Honest scoping remark

The authoritative Gate-1A source definitions (`ω`, `τ`, `Σ_i`, `F_i`, `g`, the clean
cells and the physical ranges) are **not present in this repository**.  Rather than
invent them — which would produce a theorem whose name matched the target but whose
content did not — we state the challenge against an explicit abstract *two-view source*
interface: two synchronized congruence conditions `F₁ i = 0`, `F₂ i = 0` on a finite
index type, with the fibre count being the cardinality of the simultaneous zero set.
Supplying the authoritative definitions means instantiating `TwoViewSource`; that
instantiation is itself an open source-glue task (Challenge C).

What *is* proved here is only the portability statement inherited from the trusted
bank: the fibre count is invariant under fixed-unit twists of `F₁, F₂`.  This is
Bank C and it is **not** a proof of SB-ν.
-/

open scoped BigOperators

namespace Challenges
namespace Gate1A

open TrustedBank.ZeroSetTransport

/-- An abstract synchronized two-view source at scale `X`: a finite index type with two
congruence functions into `ZMod q₁`, `ZMod q₂`. -/
structure TwoViewSource where
  /-- the scale parameter -/
  X : ℕ
  /-- the index type of the source (cells) -/
  I : Type
  /-- finiteness of the index type -/
  fin : Fintype I
  /-- decidable equality on the index type -/
  dec : DecidableEq I
  /-- the first modulus -/
  q₁ : ℕ
  /-- the second modulus -/
  q₂ : ℕ
  /-- the first view -/
  F₁ : I → ZMod q₁
  /-- the second view -/
  F₂ : I → ZMod q₂

attribute [instance] TwoViewSource.fin TwoViewSource.dec

open Classical in
/-- The synchronized two-view fibre: the set of cells killed by both views. -/
noncomputable def fibre (S : TwoViewSource) : Finset S.I :=
  Finset.univ.filter (fun i => S.F₁ i = 0 ∧ S.F₂ i = 0)

open Classical in
/-- The fibre multiplicity `N_ν` of the source. -/
noncomputable def fibreCount (S : TwoViewSource) : ℕ := (fibre S).card

/-- **The Gate-1A target, as a statement (OPEN).**  A family of sources indexed by the
scale has `X^{o(1)}` fibre multiplicity if for every `ε > 0` there is a constant with
`N_ν(X) ≤ C_ε X^ε` for all large `X`.

This is a `Prop`-valued definition, deliberately **not** a theorem: it is the open
analytic target. -/
def SubpolynomialFibre (fam : ℕ → TwoViewSource) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧ ∀ X : ℕ, 1 ≤ X →
    (fibreCount (fam X) : ℝ) ≤ Cε * (X : ℝ) ^ ε

/-- Two sources are *unit-twisted copies* of each other when their views differ by
fixed units. -/
def UnitTwisted (S T : TwoViewSource) : Prop :=
  ∃ h : S.I = T.I, ∃ (κ₁ : (ZMod S.q₁)ˣ) (κ₂ : (ZMod S.q₂)ˣ) (e₁ : ZMod T.q₁ ≃ ZMod S.q₁)
    (e₂ : ZMod T.q₂ ≃ ZMod S.q₂), (∀ i : S.I, e₁ (T.F₁ (h ▸ i)) = (κ₁ : ZMod S.q₁) * S.F₁ i) ∧
      (∀ i : S.I, e₂ (T.F₂ (h ▸ i)) = (κ₂ : ZMod S.q₂) * S.F₂ i) ∧
      e₁ 0 = 0 ∧ e₂ 0 = 0

/-- **Portability (proved, from Bank C).**  Twisting the two views by fixed units does
not change the simultaneous zero set, hence not the fibre count.  This is stated for
one source and its literal unit twist. -/
theorem fibreCount_twist (S : TwoViewSource) (κ₁ : (ZMod S.q₁)ˣ) (κ₂ : (ZMod S.q₂)ˣ) :
    fibreCount { S with F₁ := twist κ₁ S.F₁, F₂ := twist κ₂ S.F₂ } = fibreCount S := by
  classical
  unfold fibreCount fibre
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact twist_simultaneous_zero_iff S.F₁ S.F₂ κ₁ κ₂ i

/-- **Consequence (proved).**  The open SB-ν property is invariant under fixed-unit
twisting of the whole family.  This is exactly the portability content that the trusted
bank supplies; it does **not** prove SB-ν for any family. -/
theorem subpolynomialFibre_twist (fam : ℕ → TwoViewSource)
    (κ₁ : ∀ X, (ZMod (fam X).q₁)ˣ) (κ₂ : ∀ X, (ZMod (fam X).q₂)ˣ)
    (h : SubpolynomialFibre fam) :
    SubpolynomialFibre (fun X => { fam X with
      F₁ := twist (κ₁ X) (fam X).F₁, F₂ := twist (κ₂ X) (fam X).F₂ }) := by
  intro ε hε
  obtain ⟨Cε, hCε, hbound⟩ := h ε hε
  refine ⟨Cε, hCε, fun X hX => ?_⟩
  rw [fibreCount_twist]
  exact hbound X hX

/-! ## First remaining theorem for Gate 1A

Instantiate `TwoViewSource` with the authoritative source data and prove
`SubpolynomialFibre` for it.  No part of that is available here: neither the source
definitions nor any divisor-type bound sufficient for TF4.  We record the target as a
statement only, and add **no** axiom. -/

end Gate1A
end Challenges
