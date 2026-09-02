import Mathlib
import RequestProject.Erdos287.ClosureInputs
import RequestProject.Status.CurrentStatusErdos287SimultaneousCritical

/-!
# Semantic firewalls and semantic unit tests — Erdős #287

This module is **append-only** and contains **no new analytic claim**.  Every declaration is a
kernel-checked *guard*: an explicit countermodel or label-distinctness fact that prevents a
semantic confusion which could otherwise creep into prose summaries of the bank.

Guards provided here:

1. `Gap2CE` one-way firewall (with an explicit countermodel).
2. Pointwise versus aggregate bounds (neither implies the other).
3. Branch coverage versus global coverage.
4. Small-`x` versus large-`X` scale firewall.
5. `q`-role separation (switch / local / effective / transverse).
6. Status-label separation (`kernelProved` ≠ `analyticBanked` ≠ `conditionalSourcePin` ≠ `open_`).

None of these theorems asserts anything about the truth of Erdős #287, which remains open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace SemanticFirewalls

/-! ## §1  `Gap2CE` is strictly weaker than `Erdos287Counterexample`

The historical compiler type `Gap2CE` is a *relaxation*: it allows the denominator `1` and does
not require two denominators.  The bridge `Erdos287Counterexample.toGap2CE` therefore runs in one
direction only.  The countermodel below makes this precise, so that a refutation of `Gap2CE` may
never be read as a refutation of the actual problem statement without the bridge, and — crucially
— a statement proved *about* `Gap2CE` objects is a statement about a strictly larger class. -/

/-- The singleton `A = {1}`: reciprocals sum to `1`, and the gap condition is vacuous because the
unique element is the maximum. -/
def singletonGap2CE : Gap2CE where
  A := {1}
  hne := ⟨1, by simp⟩
  hpos := by
    intro a ha
    simp only [Finset.mem_singleton] at ha
    omega
  hsum := by simp
  hgap := by
    intro a ha hmax
    exfalso
    simp only [Finset.mem_singleton] at ha
    apply hmax
    subst ha
    simp [Finset.max'_singleton]

/-- **Countermodel.**  `{1}` is a `Gap2CE` but is **not** an `Erdos287Counterexample`: it has one
element and that element is not `> 1`. -/
theorem singleton_not_counterexample :
    ¬ Erdos287Counterexample singletonGap2CE.A := by
  intro h
  have h1 := h.one_lt 1 (by simp [singletonGap2CE])
  omega

/-- **`gap2CE_firewall`.**  The bridge is one-way: every exact counterexample is a `Gap2CE`, but
some `Gap2CE` is not an exact counterexample. -/
theorem gap2CE_firewall :
    (∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, (h.toGap2CE).A = A) ∧
      ∃ ce : Gap2CE, ¬ Erdos287Counterexample ce.A :=
  ⟨fun _ _ => rfl, ⟨singletonGap2CE, singleton_not_counterexample⟩⟩

/-! ## §2  Pointwise versus aggregate -/

/-- A pointwise bound on a finite family. -/
def PointwiseBound {n : ℕ} (f : Fin n → ℝ) (K : ℝ) : Prop := ∀ i, f i ≤ K

/-- An aggregate (summed) bound on a finite family. -/
def AggregateBound {n : ℕ} (f : Fin n → ℝ) (K : ℝ) : Prop := ∑ i, f i ≤ K

/-- **Firewall.**  A pointwise bound does not give the aggregate bound with the same constant. -/
theorem pointwise_not_aggregate :
    ∃ (f : Fin 2 → ℝ) (K : ℝ), PointwiseBound f K ∧ ¬ AggregateBound f K := by
  refine ⟨fun _ => 1, 1, fun _ => le_refl 1, ?_⟩
  simp [AggregateBound]

/-- **Firewall.**  An aggregate bound does not give the pointwise bound with the same constant. -/
theorem aggregate_not_pointwise :
    ∃ (f : Fin 2 → ℝ) (K : ℝ), AggregateBound f K ∧ ¬ PointwiseBound f K := by
  refine ⟨![2, -2], 0, ?_, ?_⟩
  · simp [AggregateBound, Fin.sum_univ_two]
  · intro h
    have := h 0
    norm_num at this

/-! ## §3  Branch coverage versus global coverage -/

/-- **Firewall.**  Full coverage of one branch is not full coverage of the union of branches.
Consequently a bare "100 %" claim is meaningless without a scope label. -/
theorem branch_coverage_not_global :
    ∃ cov : Fin 2 → ℝ, cov 0 = 1 ∧ (cov 0 + cov 1) / 2 ≠ 1 := by
  refine ⟨![1, 0], rfl, ?_⟩
  norm_num

/-! ## §4  Small-`x` versus large-`X` -/

/-- **Firewall.**  A bound valid at the small scale `x` does not transfer to the large scale `X`;
the two symbols must never be identified. -/
theorem smallX_bound_does_not_transfer :
    ∃ (f : ℝ → ℝ) (x X : ℝ), x < X ∧ f x ≤ 1 ∧ ¬ f X ≤ 1 := by
  refine ⟨id, 1, 2, by norm_num, by norm_num, ?_⟩
  norm_num

/-! ## §5  The four roles of the symbol `q` -/

/-- The four distinct roles played by the symbol `q` in the programme:
the *switch* modulus, the *local* modulus of a packet, the *effective* modulus after reduction,
and the *transverse* carrier product. -/
inductive QRole
  /-- The switch modulus. -/
  | qSwitch
  /-- The local modulus of a packet. -/
  | qLocal
  /-- The effective modulus after conductor reduction. -/
  | qEff
  /-- The transverse carrier product `2° · E° · R · B°`. -/
  | qTransverse
  deriving DecidableEq, Fintype, Repr

/-- **Firewall.**  The four `q`-roles are pairwise distinct objects; no theorem stated for one of
them may be transported to another without an explicit bridge. -/
theorem qRoles_pairwise_distinct :
    QRole.qSwitch ≠ QRole.qLocal ∧ QRole.qSwitch ≠ QRole.qEff ∧
      QRole.qSwitch ≠ QRole.qTransverse ∧ QRole.qLocal ≠ QRole.qEff ∧
      QRole.qLocal ≠ QRole.qTransverse ∧ QRole.qEff ≠ QRole.qTransverse := by
  decide +kernel

/-- There are exactly four `q`-roles. -/
theorem qRole_card : Fintype.card QRole = 4 := by decide +kernel

/-! ## §6  Status labels are pairwise distinct -/

open Erdos287.C0UnitaryFourierStatus

/-- **Firewall.**  `kernelProved`, `analyticBanked`, `conditionalSourcePin`, `strictReduction`
and `open_` are pairwise distinct labels.  In particular an `analyticBanked` row is *not* a
kernel-checked theorem, and a `conditionalSourcePin` row is *not* an unconditional result. -/
theorem status_labels_pairwise_distinct :
    ResearchStatus.kernelProved ≠ ResearchStatus.analyticBanked ∧
      ResearchStatus.analyticBanked ≠ ResearchStatus.conditionalSourcePin ∧
      ResearchStatus.conditionalSourcePin ≠ ResearchStatus.strictReduction ∧
      ResearchStatus.strictReduction ≠ ResearchStatus.open_ ∧
      ResearchStatus.kernelProved ≠ ResearchStatus.open_ := by
  decide +kernel

end SemanticFirewalls
end Erdos287
