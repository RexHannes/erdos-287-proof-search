import Mathlib
import RequestProject.Erdos287.ClosureInputs
import RequestProject.CurrentProgramme.Erdos287FCLAlgebraicBridge

/-!
# The window-pair export interface and the effectivity firewall

`WINDOWPAIR EXPORT : OPEN unless supplied`
`EFFECTIVITY      : OPEN unless supplied`

Two separate things are formalised here.

**§1 — the export dictionary.**  `FixedCertificatePrimeMassToWindowPairInput` is the exact
bridge that the mathematical run would have to supply: positive certificate prime mass at
`M`, *together with* the literal window-pair data.  Its conclusion is literally
`Erdos287.WindowPairSupply M`.  It is **left uninhabited**.

**§2 — the effectivity firewall.**  `EventualSupply p` (a bare `∃ M₀`) and `EffectiveSupply
p` (a structure *carrying* the natural number `M₀`) are kept apart, and whether
`M₀ ≤ 4·10⁹` is recorded as a separate predicate.  A non-effective "for all sufficiently
large `M`" is never converted into a `Nat` witness: the counterguard
`eventual_does_not_give_bounded_effective` shows that even a genuine eventual supply need
not admit any `M₀` inside the kernel-verified finite range.

**§3 — the end-to-end adapter.**  *Conditionally* on a bounded effective supply, the banked
compiler yields `Erdos287.Erdos287Statement`.  Neither premise is inhabited, so **Erdős #287
remains OPEN**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace WindowPairExport

open Erdos287.FixedCertificate

/-! ## §1.  The export dictionary -/

/-- **`FixedCertificatePrimeMassToWindowPairInput`** — `SOURCE_OPEN / UNINHABITED`.

The literal bridge from the fixed-certificate prime-mass conclusion at `M` to the window
pair at `M`.  Every field of `Erdos287.WindowPairSupply` is present explicitly, and the
prime-mass hypothesis records that this is the *export* of the FCL conclusion, not an
independent guess. -/
structure FixedCertificatePrimeMassToWindowPairInput
    (d : FixedCertificateData) (M x pu au pv av : ℕ) : Prop where
  /-- The FCL conclusion at `M`: the certificate-positive region carries prime mass. -/
  prime_mass_positive : 0 < ∑ p ∈ d.P, d.a p
  /-- `pu` is prime. -/
  u_prime : pu.Prime
  /-- `pv` is prime. -/
  v_prime : pv.Prime
  /-- The first exponent is at least one. -/
  u_exp : 1 ≤ au
  /-- The second exponent is at least one. -/
  v_exp : 1 ≤ av
  /-- Divisibility at `x`. -/
  u_dvd : pu ^ au ∣ x
  /-- Divisibility at `x + 1`. -/
  v_dvd : pv ^ av ∣ (x + 1)
  /-- The first window is at most `9`. -/
  u_window : M / pu ^ au ≤ 9
  /-- The certified numerator inequality at the first window. -/
  u_cval : CVal (M / pu ^ au) < pu
  /-- The second window is at most `9`. -/
  v_window : M / pv ^ av ≤ 9
  /-- The certified numerator inequality at the second window. -/
  v_cval : CVal (M / pv ^ av) < pv
  /-- `x` lies in the top half. -/
  lower : M ≤ 2 * x
  /-- `x + 1` does not exceed `M`. -/
  upper : x + 1 ≤ M

/-- **`windowPairSupply_of_export`.**  `CONDITIONAL_COMPILER / KERNEL-PROVED`.

The export dictionary yields the literal window-pair supply at `M`. -/
theorem windowPairSupply_of_export {d : FixedCertificateData} {M x pu au pv av : ℕ}
    (h : FixedCertificatePrimeMassToWindowPairInput d M x pu au pv av) :
    WindowPairSupply M :=
  ⟨x, pu, au, pv, av, h.u_prime, h.v_prime, h.u_exp, h.v_exp, h.u_dvd, h.v_dvd,
    h.u_window, h.u_cval, h.v_window, h.v_cval, h.lower, h.upper⟩

/-- **`export_input_not_automatic`.**  `KERNEL-PROVED`.  The export dictionary is a genuine
obligation: explicit data refute it. -/
theorem export_input_not_automatic :
    ∃ (d : FixedCertificateData) (M x pu au pv av : ℕ),
      ¬ FixedCertificatePrimeMassToWindowPairInput d M x pu au pv av := by
  classical
  refine ⟨⟨∅, ∅, ∅, fun _ => 0, fun _ => 0, fun _ => 0, by simp, by simp, by simp, by simp,
    by simp, by simp⟩, 0, 0, 0, 0, 0, 0, ?_⟩
  intro h
  exact Nat.not_prime_zero h.u_prime

/-! ## §2.  The effectivity firewall -/

/-- **`EventualSupply`** — the *non-effective* form: some threshold exists. -/
def EventualSupply (p : ℕ → Prop) : Prop := ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → p M

/-- **`EffectiveSupply`** — the *effective* form: the threshold is carried as data. -/
structure EffectiveSupply (p : ℕ → Prop) where
  /-- The explicit threshold. -/
  M0 : ℕ
  /-- The supply above the threshold. -/
  supply : ∀ M : ℕ, M0 ≤ M → p M

/-- Whether the effective threshold lies inside the kernel-verified finite range. -/
def EffectiveSupply.Bounded {p : ℕ → Prop} (s : EffectiveSupply p) : Prop :=
  s.M0 ≤ 4000000000

/-- An effective supply is in particular an eventual one. -/
theorem eventual_of_effective {p : ℕ → Prop} (s : EffectiveSupply p) : EventualSupply p :=
  ⟨s.M0, s.supply⟩

/-- **`eventual_does_not_give_bounded_effective`.**  `KERNEL-PROVED`.

The effectivity firewall.  A genuine eventual supply need not admit **any** threshold inside
the kernel-verified finite range: no "sufficiently large" statement may be converted into a
bounded `Nat` witness. -/
theorem eventual_does_not_give_bounded_effective :
    ∃ p : ℕ → Prop, EventualSupply p ∧ ∀ s : EffectiveSupply p, ¬ s.Bounded := by
  refine ⟨fun M => 4000000001 ≤ M, ⟨4000000001, fun _ h => h⟩, ?_⟩
  intro s hb
  have h := s.supply 4000000000 (le_trans hb (le_refl _))
  omega

/-- The window-pair supply in eventual form.  **Not proved anywhere.** -/
def EventualWindowPairSupply : Prop := EventualSupply WindowPairSupply

/-- The window-pair supply in effective form.  **Not constructed anywhere.** -/
abbrev EffectiveWindowPairSupply := EffectiveSupply WindowPairSupply

/-! ## §3.  The end-to-end adapter (conditional) -/

/-- **`closureInputs_of_boundedEffective`.**  `KERNEL-PROVED` (conditional).

A bounded effective window-pair supply is exactly the banked `Erdos287ClosureInputs`. -/
def closureInputs_of_boundedEffective (s : EffectiveWindowPairSupply) (h : s.Bounded) :
    Erdos287ClosureInputs where
  M0 := s.M0
  threshold_covered := h
  supply := s.supply

/-- **`erdos287Statement_of_boundedEffective`.**  `CONDITIONAL_COMPILER / KERNEL-PROVED`.

*If* a bounded effective window-pair supply is ever supplied, the banked end-to-end compiler
yields the exact public statement of Erdős #287.  **Neither premise is inhabited in this
repository, so nothing about #287 is proved here.** -/
theorem erdos287Statement_of_boundedEffective (s : EffectiveWindowPairSupply)
    (h : s.Bounded) : Erdos287Statement :=
  no_Erdos287Counterexample_of_closure (closureInputs_of_boundedEffective s h)

/-- The adapter consumes an *effective* supply: the eventual form alone is not enough, by
the firewall above. -/
theorem adapter_needs_effective_supply :
    ∃ p : ℕ → Prop, EventualSupply p ∧ ∀ s : EffectiveSupply p, ¬ s.Bounded :=
  eventual_does_not_give_bounded_effective

end WindowPairExport
end Erdos287
