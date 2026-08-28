import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger
import RequestProject.Erdos287.OffDiagonal3221
import RequestProject.Erdos287.EHNoWrap3221

/-!
# V17, Phase E — the completed 3221 source dictionary and the DI/Kuznetsov socket

## §15.  There is **no** completed Poisson/Fourier source in this repository

A repository-wide search finds no completed Fourier expansion, no additive-character sum,
no Poisson summation identity and no `e_q(·)` object anywhere in the Lean sources.  The
schematic post-Poisson expression of the Pro run therefore **cannot** be derived here, and
per instruction it is *not* created as a theorem.

Instead `BalancedSeven3221CompletedSource` is a **source dictionary**: a record of concrete
finite data together with concrete equalities and support conditions.  It has no free `Prop`
field.  No physical instance is constructed anywhere in this project.

## §16.  The analytic socket

`DIKuznetsov3221Input` is a source-specific, never-inhabited interface: it states one
concrete bound for the *already defined* completed value carried by a given dictionary.  It
is **not** a generic Kuznetsov axiom, and it is **not** an `axiom` at all — it is a
`Prop`-valued structure with no inhabitant in this project.

`3221-DI-KUZNETSOV-LITERAL-SPLICE45 : OPEN_ANALYTIC / UNINHABITED.`

## §17.  Theorem-slot dictionary metadata and counterguards

`DISlotAssignment` records the shape of a proposed DI dictionary (`r, s, m, n, c` slots,
modulus factorisation, coprimality).  `slot_dependence_counterguard` and
`zeroMode_separation_guard` are proved counterguards: an illegal coefficient dependence
cannot be relabelled away, and a separated zero mode cannot be silently reabsorbed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace Erdos287
namespace DI3221

/-! ## §15. The completed-source dictionary -/

/-- **`3221-COMPLETED-SOURCE-DICTIONARY45` — `SOURCE_OPEN`.**

A record of the finite data a completed 3221 off-diagonal source would have to supply,
with every field a concrete equality, inequality or support condition on that data (no free
`Prop` field).  The two *values* `parentValue` and `completedValue` are the exact source
parent value and the exact completed off-diagonal value; `completion` is the routed-error
equality relating them.

**No physical inhabitant is constructed anywhere in this project.**  The structure is a
data record, so degenerate data (empty boxes) would satisfy it; that is precisely why the
analytic content is *not* placed here but in `DIKuznetsov3221Input`, which is never
inhabited at all. -/
structure BalancedSeven3221CompletedSource where
  /-- The modulus box `q ∼ Q`. -/
  Qbox : Finset ℕ
  /-- The single-prime box `e ∼ E`. -/
  Ebox : Finset ℕ
  /-- The box `n ∼ N`. -/
  Nbox : Finset ℕ
  /-- The box `ℓ ∼ L`. -/
  Lbox : Finset ℕ
  /-- The dual box `|h| ≪ H`. -/
  Hbox : Finset ℤ
  /-- The fixed residue shift `a_s`. -/
  shift : ℤ
  /-- The exact source parent value. -/
  parentValue : ℂ
  /-- The exact completed off-diagonal value. -/
  completedValue : ℂ
  /-- The admitted routed-error budget. -/
  routedError : ℝ
  /-- Routed errors are nonnegative. -/
  routedError_nonneg : 0 ≤ routedError
  /-- **The completion equality, after routed errors.** -/
  completion : ‖parentValue - completedValue‖ ≤ routedError
  /-- The off-diagonal parameter. -/
  t : ℤ
  /-- Genuine off-diagonal: `t ≠ 0`. -/
  t_ne_zero : t ≠ 0
  /-- Upper bound for the source variables `w = e n ℓ`. -/
  Wmax : ℤ
  /-- Lower bound for the moduli. -/
  Qmin : ℤ
  /-- Moduli are positive. -/
  Qmin_pos : 0 < Qmin
  /-- The `t` support, in the exact finite form proved in `OffDiagonal3221`. -/
  t_support : |t| * Qmin ≤ 2 * Wmax
  /-- Upper bound for the dual variable. -/
  Hmax : ℤ
  /-- The `|h|` support. -/
  h_support : ∀ h ∈ Hbox, |h| ≤ Hmax
  /-- Unit/inverse support: every `e` is invertible modulo every modulus. -/
  unit_support : ∀ q ∈ Qbox, ∀ e ∈ Ebox, Nat.Coprime e q
  /-- `h = 0` separation: the zero mode is *not* part of the completed sum. -/
  zero_mode_separated : (0 : ℤ) ∉ Hbox
  /-- Nonunit routing: the `n ℓ` part is invertible modulo every modulus. -/
  nonunit_routing : ∀ q ∈ Qbox, ∀ n ∈ Nbox, ∀ l ∈ Lbox, Nat.Coprime (n * l) q
  /-- The low-conductor cut. -/
  lowConductorCut : ℕ
  /-- Low-conductor separation: small moduli are routed elsewhere. -/
  lowConductor_separated : ∀ q ∈ Qbox, lowConductorCut < q

namespace BalancedSeven3221CompletedSource

variable (S : BalancedSeven3221CompletedSource)

/-- From the completion field: the parent value is controlled by the completed value plus
the routed error. -/
theorem parent_norm_le : ‖S.parentValue‖ ≤ ‖S.completedValue‖ + S.routedError := by
  have h : ‖S.parentValue‖ ≤ ‖S.parentValue - S.completedValue‖ + ‖S.completedValue‖ := by
    calc ‖S.parentValue‖ = ‖(S.parentValue - S.completedValue) + S.completedValue‖ := by
          congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith [S.completion]

/-- The dictionary's `t`-support is exactly the finite range proved in Phase C. -/
theorem t_range_of_source {w₁ w₂ q : ℤ} (hW₁ : |w₁| ≤ S.Wmax) (hW₂ : |w₂| ≤ S.Wmax)
    (hQ : S.Qmin ≤ |q|) (ht : w₁ - w₂ = q * S.t) :
    |S.t| * S.Qmin ≤ 2 * S.Wmax :=
  Erdos287.OffDiag3221.offdiag_abs_t_le hW₁ hW₂ hQ ht

end BalancedSeven3221CompletedSource

/-! ## §16. The DI/Kuznetsov analytic socket -/

/-- **`3221-DI-KUZNETSOV-LITERAL-SPLICE45` — `OPEN_ANALYTIC / UNINHABITED`.**

The single analytic input required by the 3221 reduction, stated *for one specific
completed source dictionary*: the completed nondegenerate off-diagonal value satisfies
`|O| ≤ X^{39/35 - η}` for a fixed `η > 0`.

This is **not** a generic Kuznetsov/Deshouillers–Iwaniec theorem, **not** an `axiom`, and
**no inhabitant is provided anywhere in this project**.  Any future inhabitant must be a
genuine analytic proof for the specific source `S`. -/
structure DIKuznetsov3221Input (S : BalancedSeven3221CompletedSource) (X eta : ℝ) : Prop where
  /-- Asymptotic regime. -/
  X_gt_one : 1 < X
  /-- A fixed positive saving. -/
  eta_pos : 0 < eta
  /-- **The open analytic estimate.** -/
  bound : ‖S.completedValue‖ ≤ X ^ ((39 / 35 : ℝ) - eta)

/-- The pre-splice target exponent `39/35` exceeds `1` by exactly the off-diagonal
parameter exponent `Texp = 4/35` — capacity bookkeeping only. -/
theorem preSplice_target_gap : (39 : ℚ) / 35 - 1 = Erdos287.Ledger3221.Texp :=
  Erdos287.Ledger3221.preSplice_target_gap

/-! ## §17. Theorem-slot dictionary metadata -/

/-- The shape of a proposed DI dictionary: the five theorem slots together with the
modulus factorisation and coprimality data.  Recording the shape is **not** asserting that
such a dictionary exists for the physical source. -/
structure DISlotAssignment where
  /-- The `r` slot (first modulus factor). -/
  rSlot : ℕ
  /-- The `s` slot (second modulus factor). -/
  sSlot : ℕ
  /-- The `m` slot. -/
  mSlot : ℕ
  /-- The `n` slot (fixed phase variable). -/
  nSlot : ℕ
  /-- The `c` slot (the weight variable the coefficients may **not** depend on). -/
  cSlot : ℕ
  /-- The modulus. -/
  modulus : ℕ
  /-- Modulus factorisation `q = r s`. -/
  modulus_factorisation : modulus = rSlot * sSlot
  /-- The two factors are coprime. -/
  coprime_rs : Nat.Coprime rSlot sSlot
  /-- The fixed `n`-phase condition: `n` is invertible modulo the modulus. -/
  n_phase : Nat.Coprime nSlot modulus
  /-- The `m` slot is invertible modulo the modulus. -/
  m_unit : Nat.Coprime mSlot modulus

/-- **Counterguard: an illegal coefficient dependence cannot be relabelled away.**
If a coefficient family genuinely depends on the `c` slot (two `c` values give different
coefficient functions), then it cannot be rewritten as a `c`-independent family. -/
theorem slot_dependence_counterguard {β : Type*} (f : ℕ → ℕ → β) (c₁ c₂ : ℕ)
    (hne : f c₁ ≠ f c₂) : ¬ ∃ g : ℕ → β, ∀ c m, f c m = g m := by
  rintro ⟨g, hg⟩
  exact hne (funext fun m => (hg c₁ m).trans (hg c₂ m).symm)

/-- **Counterguard: a separated zero mode cannot be silently reabsorbed.**
Adding the mode `h = 0` back to a sum over a zero-free dual box changes the value unless
the zero mode itself vanishes. -/
theorem zeroMode_separation_guard (Hbox : Finset ℤ) (h0 : (0 : ℤ) ∉ Hbox) (f : ℤ → ℂ) :
    (∑ h ∈ insert (0 : ℤ) Hbox, f h = ∑ h ∈ Hbox, f h) ↔ f 0 = 0 := by
  rw [Finset.sum_insert h0]
  constructor
  · intro h; exact add_eq_right.mp h
  · intro h; rw [h, zero_add]

/-- **Counterguard: the modulus factorisation is data, not a consequence.**  A modulus can
admit several coprime factorisations, so the `(r,s)` slots must be *carried*, never
inferred.  Witness: `6 = 1·6 = 2·3` with both factorisations coprime. -/
theorem modulus_factorisation_not_unique :
    ∃ r₁ s₁ r₂ s₂ : ℕ, r₁ * s₁ = 6 ∧ r₂ * s₂ = 6 ∧ Nat.Coprime r₁ s₁ ∧ Nat.Coprime r₂ s₂ ∧
      (r₁, s₁) ≠ (r₂, s₂) := by
  refine ⟨1, 6, 2, 3, by norm_num, by norm_num, by decide, by decide, by decide⟩

end DI3221
end Erdos287
