import Mathlib
import RequestProject.TrustedBank.Interfaces.ZeroSetTransport
import RequestProject.TrustedBank.Interfaces.FiniteSumTransport
import RequestProject.TrustedBank.FixedAffine.Basic

/-!
# Challenge C — fixed-affine source glue  (**OPEN**)

**Status: OPEN.**  Nothing here is imported by `TrustedBank/`.

Bank C proves that a fixed-unit twist of the two views changes neither the simultaneous
zero set nor its cardinality.  What it does *not* prove — and what must not be inferred
from it — is that passing from the base (twin) source packet to a fixed affine source
packet *is* such a twist.  That is the source-glue statement, and it is open: it
requires mapping every source coefficient, every normalisation, and every exceptional
cell.

This file records the glue as an explicit predicate, states precisely what the affine
normal form (Bank A) already contributes, and proves the one implication that is
genuinely available: **if** the glue holds by unit reindexing away from finitely many
bad primes, **then** the fibre counts agree.
-/

open scoped BigOperators

namespace Challenges
namespace AffineGlue

open TrustedBank.ZeroSetTransport TrustedBank.FixedAffine

/-- The affine normal-form input that Bank A supplies for one good prime: with `a₁, a₂`
and the determinant `Δ` invertible mod `p`, the two forbidden residues of the affine
pair are `{0, -Δ/a₂}` in the coordinate `m = L₁(n)`, and the fixed unit `-a₂/Δ`
normalises them to the canonical pair `{0, 1}`. -/
theorem affine_normal_form_at_good_prime {p : ℕ} [Fact (Nat.Prime p)]
    {a₁ b₁ a₂ b₂ : ZMod p} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hΔ : det a₁ b₁ a₂ b₂ ≠ 0) :
    (∀ n : ZMod p, lin a₂ b₂ n = 0 ↔ lin a₁ b₁ n = -(det a₁ b₁ a₂ b₂) / a₂) ∧
      (fun x : ZMod p => normUnit a₁ b₁ a₂ b₂ * x) ''
        ({0, -(det a₁ b₁ a₂ b₂) / a₂} : Set (ZMod p)) = ({0, 1} : Set (ZMod p)) :=
  ⟨fun _ => second_root_iff ha₁ ha₂ rfl, normUnit_image_roots ha₂ hΔ⟩

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R₁ R₂ : Type*} [MonoidWithZero R₁] [MonoidWithZero R₂]

/-- **The open glue statement.**  The affine packet `(G₁, G₂)` is *unit-glued* to the
base packet `(F₁, F₂)` when it is obtained from it by multiplication by fixed units.
This is a `Prop`-valued definition; asserting it for the authoritative source data is
exactly the open task. -/
def UnitGlued (F₁ G₁ : I → R₁) (F₂ G₂ : I → R₂) : Prop :=
  ∃ (κ₁ : R₁ˣ) (κ₂ : R₂ˣ), G₁ = twist κ₁ F₁ ∧ G₂ = twist κ₂ F₂

omit [DecidableEq I] in
/-- **Proved.**  If the glue holds, the simultaneous zero sets are literally equal —
so the affine fibre count equals the base fibre count. -/
theorem zeroSet_eq_of_unitGlued {F₁ G₁ : I → R₁} {F₂ G₂ : I → R₂}
    (h : UnitGlued F₁ G₁ F₂ G₂)
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => G₁ i = 0 ∧ G₂ i = 0] :
    zeroSet G₁ G₂ = zeroSet F₁ F₂ := by
  obtain ⟨κ₁, κ₂, rfl, rfl⟩ := h
  ext i
  simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact twist_simultaneous_zero_iff F₁ F₂ κ₁ κ₂ i

omit [DecidableEq I] in
/-- **Proved.**  The fibre counts agree under the glue. -/
theorem card_eq_of_unitGlued {F₁ G₁ : I → R₁} {F₂ G₂ : I → R₂}
    (h : UnitGlued F₁ G₁ F₂ G₂)
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => G₁ i = 0 ∧ G₂ i = 0] :
    (zeroSet G₁ G₂).card = (zeroSet F₁ F₂).card := by
  rw [zeroSet_eq_of_unitGlued h]

/-- **The residual open statement, with the finitely many bad primes made explicit.**
Full affine transference would be: for every fixed affine source there is a finite set
of bad primes outside of which the packet is unit-glued to the base packet, *and* the
bad cells contribute a bounded amount.  Recorded as a `Prop`; **not** proved. -/
def AffineTransference
    (badPrimes : Finset ℕ)
    (glue : ∀ p : ℕ, p ∉ badPrimes → Prop) : Prop :=
  ∀ p : ℕ, ∀ hp : p ∉ badPrimes, glue p hp

end AffineGlue
end Challenges
