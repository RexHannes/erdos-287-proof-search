import Mathlib
import RequestProject.TrustedBank.Interfaces.ZeroSetTransport

/-!
# Trusted bank — finite-sum transport interface

Small interface layer: transporting finite sums and finite bounds along a bijection of
index sets, and along a fixed-unit twist of the fibre functions (Bank C).

These are the only "transport" facts that the trusted bank exports; no analytic
statement is made or assumed here.
-/

open scoped BigOperators

namespace TrustedBank
namespace FiniteSumTransport

/-- Transport of a finite sum along a bijection of index types. -/
theorem sum_equiv_transport {I J : Type*} [Fintype I] [Fintype J] {M : Type*}
    [AddCommMonoid M] (e : I ≃ J) (f : J → M) : ∑ i, f (e i) = ∑ j, f j :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Transport of a finite *bound* along a bijection of index types. -/
theorem sum_le_transport {I J : Type*} [Fintype I] [Fintype J] {M : Type*}
    [AddCommMonoid M] [Preorder M] (e : I ≃ J) (f : J → M) {B : M} (h : ∑ j, f j ≤ B) :
    ∑ i, f (e i) ≤ B := by
  rwa [sum_equiv_transport e f]

open ZeroSetTransport

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {R₁ R₂ : Type*} [MonoidWithZero R₁] [MonoidWithZero R₂]

omit [DecidableEq I] in
/-- **Bank C, bound form.**  A bound on the (weighted) simultaneous-fibre count of a
family transports verbatim to any fixed-unit twist of that family. -/
theorem twisted_fibre_bound_transport
    (F₁ : I → R₁) (F₂ : I → R₂) (κ₁ : R₁ˣ) (κ₂ : R₂ˣ)
    [DecidablePred fun i => F₁ i = 0 ∧ F₂ i = 0]
    [DecidablePred fun i => twist κ₁ F₁ i = 0 ∧ twist κ₂ F₂ i = 0]
    {B : ℕ} (h : (zeroSet F₁ F₂).card ≤ B) :
    (zeroSet (twist κ₁ F₁) (twist κ₂ F₂)).card ≤ B := by
  rwa [twist_zeroSet_card_eq]

end FiniteSumTransport
end TrustedBank
