import Mathlib
import RequestProject.HostileAudit.BalancedSevenSP2SourceAdapter
import RequestProject.HostileAudit.GeneralModulusConductorSplitLargeSieve
import RequestProject.HostileAudit.SmallROwnerCapacity
import RequestProject.HostileAudit.ShiuHypothesisCompiler
import RequestProject.HostileAudit.HardAmplitudeExponentCompiler
import RequestProject.HostileAudit.FullQExactReassembly
import RequestProject.HostileAudit.EffectiveLowConductorExceptionalPNT

/-!
# Hostile-audit safe bank §13 — the Balanced7 conditional closure compiler

`BalancedSevenHostileAuditInputs` bundles **exactly** the eight ingredients that the hostile
audit identified:

1. the SP-2 source adapter (§2, `SOURCE_OPEN`);
2. the SmallQ low-conductor input;
3. the primitive large-sieve input (§5, uninhabited);
4. the general-modulus compiler inputs (§3–§5);
5. the SmallR direct input (§7);
6. the short-`t` sieve input (§8, uninhabited);
7. the Shiu input (§9, uninhabited);
8. the Euler principal input (§12).

together with the exact full-`q` reassembly of §12 and the per-cell savings.

`balancedSeven_hostileAudit_compiler` is a **formal conditional compiler**:

```
BalancedSevenHostileAuditInputs  →  BalancedSevenAsymptoticConclusion.
```

The structure is **not inhabited**, and it is not inhabited merely because an external audit
found the mathematics convincing (`hostileAuditInputs_not_inhabited_here`,
`hostile_audit_is_not_a_lean_proof`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

open Erdos287.CurrentProgramme
open FullQCell

/-! ## §13.1  The input bundle -/

/-- **`BalancedSevenHostileAuditInputs`** — the eight audited ingredients, plus the exact
reassembly and the per-cell savings.  `UNINHABITED`. -/
structure BalancedSevenHostileAuditInputs
    (S : ℝ → ℝ) (cellVal : FullQCell → ℝ → ℝ)
    (sourceAdapter smallQLowConductor primitiveLargeSieve generalModulusCompiler
      smallRDirect shortTSieve shiu eulerPrincipal : Prop) : Prop where
  /-- (1) The SP-2 → seven-box source adapter of §2. -/
  source_adapter : sourceAdapter
  /-- (2) The SmallQ low-conductor input. -/
  smallQ_low_conductor : smallQLowConductor
  /-- (3) The primitive weighted large-sieve input of §5. -/
  primitive_large_sieve : primitiveLargeSieve
  /-- (4) The general-modulus conductor-split compiler inputs of §3–§5. -/
  general_modulus : generalModulusCompiler
  /-- (5) The SmallR direct input of §7. -/
  smallR_direct : smallRDirect
  /-- (6) The short-`t` sieve input of §8. -/
  short_t : shortTSieve
  /-- (7) The Shiu divisor-average input of §9. -/
  shiu : shiu
  /-- (8) The Euler principal input of §12. -/
  euler_principal : eulerPrincipal
  /-- The exact full-`q` reassembly of the physical sum from the six cells (§12). -/
  reassembly : ∀ X : ℝ, S X = ∑ c : FullQCell, cellVal c X
  /-- Each cell is supplied with an `o(X / log X)` saving. -/
  cell_savings : ∀ c : FullQCell, ∀ eps : ℝ, 0 < eps →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → |cellVal c X| ≤ eps * X / Real.log X

/-! ## §13.2  The conditional compiler -/

/-- **`balancedSeven_hostileAudit_compiler`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

A purely logical implication: the audited bundle yields the Balanced7 asymptotic conclusion.
No analytic content is created. -/
theorem balancedSeven_hostileAudit_compiler
    {S : ℝ → ℝ} {cellVal : FullQCell → ℝ → ℝ}
    {sourceAdapter smallQLowConductor primitiveLargeSieve generalModulusCompiler
      smallRDirect shortTSieve shiu eulerPrincipal : Prop}
    (h : BalancedSevenHostileAuditInputs S cellVal sourceAdapter smallQLowConductor
      primitiveLargeSieve generalModulusCompiler smallRDirect shortTSieve shiu eulerPrincipal) :
    BalancedSevenAsymptoticConclusion S := by
  intro eps heps
  choose X0 hX0 using fun c : FullQCell => h.cell_savings c (eps / 6) (by positivity)
  refine ⟨Finset.univ.sup' ⟨smallQPrincipal, Finset.mem_univ _⟩ X0, ?_⟩
  intro X hX
  have hXc : ∀ c : FullQCell, X0 c ≤ X := fun c =>
    le_trans (Finset.le_sup' X0 (Finset.mem_univ c)) hX
  calc |S X| = |∑ c : FullQCell, cellVal c X| := by rw [h.reassembly X]
    _ ≤ ∑ c : FullQCell, |cellVal c X| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : FullQCell, eps / 6 * X / Real.log X :=
        Finset.sum_le_sum fun c _ => hX0 c X (hXc c)
    _ = eps * X / Real.log X := by
        rw [Finset.sum_const, Finset.card_univ]
        have hcard : (Fintype.card FullQCell : ℝ) = 6 := by
          norm_num [show Fintype.card FullQCell = 6 from by decide +kernel]
        rw [nsmul_eq_mul, hcard]
        ring

/-! ## §13.3  Firewalls -/

/-- **`hostileAuditInputs_not_inhabited_here`.**  `LEAN_PROVED`. -/
theorem hostileAuditInputs_not_inhabited_here :
    ∃ (S : ℝ → ℝ) (cellVal : FullQCell → ℝ → ℝ) (a b c d e f g i : Prop),
      ¬ BalancedSevenHostileAuditInputs S cellVal a b c d e f g i := by
  refine ⟨fun _ => 0, fun _ _ => 0, False, True, True, True, True, True, True, True, ?_⟩
  intro h
  exact h.source_adapter

/-- **`hostile_audit_is_not_a_lean_proof`.**  `LEAN_PROVED`.

Both halves of the honest statement: the compiler is a theorem, and its antecedent is not
available.  An external hostile audit of the mathematics does **not** inhabit the bundle. -/
theorem hostile_audit_is_not_a_lean_proof :
    (∀ (S : ℝ → ℝ) (cellVal : FullQCell → ℝ → ℝ) (a b c d e f g i : Prop),
        BalancedSevenHostileAuditInputs S cellVal a b c d e f g i →
          BalancedSevenAsymptoticConclusion S) ∧
      (∃ (S : ℝ → ℝ) (cellVal : FullQCell → ℝ → ℝ) (a b c d e f g i : Prop),
        ¬ BalancedSevenHostileAuditInputs S cellVal a b c d e f g i) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ h => balancedSeven_hostileAudit_compiler h,
    hostileAuditInputs_not_inhabited_here⟩

/-- **`hostileAudit_analytic_children_are_uninhabited`.**  `LEAN_PROVED`.

The four analytic children used by the bundle are each refutable by explicit data, so no
inhabitant of the bundle can be assembled from this repository. -/
theorem hostileAudit_analytic_children_are_uninhabited :
    (∃ (C : Erdos287.SP2Source.SP2FixedCertificateData) (sector : Finset ℕ) (Hs : ℕ → ℤ)
        (cut : ℕ → ℕ) (V : Fin 7 → ℝ → ℝ) (phase : Fin 7 → ℕ → ℂ) (Y : ℝ)
        (omegaSrc : Fin 7 → ℕ → ℂ),
        ¬ BalancedSevenSP2SourceSeal C sector Hs cut V phase Y omegaSrc) ∧
      (∃ (N : ℕ) (Rr : ℝ) (cells : Finset (ℕ × ℕ)) (Lval : ℕ × ℕ → ℝ) (E : ℕ → ℝ),
        ¬ PrimitiveWeightedLargeSieveInput N Rr cells Lval E) ∧
      (∃ X theta C R : ℝ, ¬ BalancedSevenShortTSieveInput X theta C R) ∧
      (∃ (Wprime s : ℕ) (Mbox : Finset ℕ) (Mlen : ℕ) (Cshiu : ℝ),
        ¬ BalancedSevenShiuInput Wprime s Mbox Mlen Cshiu) :=
  ⟨sp2SourceSeal_not_automatic, primitiveLargeSieve_not_automatic,
    shortTSieve_still_uninhabited, shiu_input_still_uninhabited⟩

end HostileAudit
end Erdos287
