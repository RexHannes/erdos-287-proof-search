import Mathlib
import RequestProject.Erdos287.DIKuznetsov3221Interface
import RequestProject.Erdos287.BalancedSeven3221Grouping
import RequestProject.Erdos287.SourceAssistedDiagonal3221
import RequestProject.Status.Erdos287V16Status

/-!
# V17, Phase F — the 3221 closure compiler

`CONDITIONAL_COMPILER`.

The logical chain represented here is

```
3221 completed-source dictionary            (SOURCE_OPEN, never inhabited physically)
  + DIKuznetsov3221Input                    (OPEN_ANALYTIC, never inhabited)
  + Endpoint3221Decomposition               (SOURCE_OPEN, never inhabited)
      ⇒ FactorialOmega7SignedEndpoint       (V16 interface)

FactorialOmega7SignedEndpoint
  + MuLogComparisonLowCondMatch             (SOURCE_BLOCKED, never inhabited)
      ⇒ BalancedSevenPacketInput            (V16 compiler, reused unchanged)
```

The second step is **not** re-proved: it is the already-banked V16 theorem
`Erdos287.V16Status.balancedSeven_of_factorialEndpoint_and_comparison`.

The first step needed an additional source-decomposition field, because the V16 endpoint
speaks about a real endpoint value `Sfac` while the 3221 child produces a complex completed
value; rather than fabricating a bridge, that bridge is made explicit as the SOURCE-OPEN
dictionary `Endpoint3221Decomposition`, whose fields are concrete inequalities relating the
two.  **Nothing in this file inhabits any analytic or source antecedent**, so no
unconditional conclusion is obtained anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Compiler3221

open Erdos287.DI3221

/-- **The additional source decomposition — `SOURCE_OPEN`, never inhabited.**

The missing link between the 3221 completed source and the V16 factorial endpoint value:
the endpoint value must be dominated by the source parent value up to the routed error, and
the analytic target plus the routed errors must fit inside the admitted budget `E`. -/
structure Endpoint3221Decomposition (S : BalancedSeven3221CompletedSource)
    (X eta Sfac E : ℝ) : Prop where
  /-- The endpoint value is dominated by the source parent value plus routed error. -/
  decomposition : |Sfac| ≤ ‖S.parentValue‖ + S.routedError
  /-- The analytic target plus two routed errors fits inside the admitted budget. -/
  budget : X ^ ((39 / 35 : ℝ) - eta) + 2 * S.routedError ≤ E

/-- **The 3221 → factorial-endpoint compiler.**  `PROVED_COMPILER / CONDITIONAL`.

Completed source dictionary + DI/Kuznetsov analytic input + endpoint decomposition
⇒ the V16 `FactorialOmega7SignedEndpoint`.  Both the analytic input and the decomposition
are uninhabited, so this theorem inhabits nothing. -/
theorem factorialEndpoint_of_3221 {X Q Sfac E eta : ℝ}
    (S : BalancedSeven3221CompletedSource)
    (hQ : Q = X ^ (3 / 5 : ℝ))
    (hDI : DIKuznetsov3221Input S X eta)
    (hdec : Endpoint3221Decomposition S X eta Sfac E) :
    Erdos287.V16Status.FactorialOmega7SignedEndpoint X Q Sfac E := by
  refine ⟨hDI.X_gt_one, hQ, ?_⟩
  have h1 : |Sfac| ≤ ‖S.parentValue‖ + S.routedError := hdec.decomposition
  have h2 : ‖S.parentValue‖ ≤ ‖S.completedValue‖ + S.routedError := S.parent_norm_le
  have h3 : ‖S.completedValue‖ ≤ X ^ ((39 / 35 : ℝ) - eta) := hDI.bound
  have h4 : X ^ ((39 / 35 : ℝ) - eta) + 2 * S.routedError ≤ E := hdec.budget
  linarith

/-- **The full 3221 → Balanced7 chain.**  `CONDITIONAL_COMPILER`.

3221 dictionary + DI/Kuznetsov socket + endpoint decomposition + the (still source-blocked)
comparison match ⇒ the V16 balanced-seven packet input, with the two error channels kept
separate (`E + err`, never merged).  Every antecedent is uninhabited. -/
theorem balancedSeven_of_3221 {X Q Sfac Sphys E err eta : ℝ}
    (S : BalancedSeven3221CompletedSource)
    (hQ : Q = X ^ (3 / 5 : ℝ))
    (hDI : DIKuznetsov3221Input S X eta)
    (hdec : Endpoint3221Decomposition S X eta Sfac E)
    (hcomp : Erdos287.V15Status.MuLogComparisonLowCondMatch X Sphys Sfac err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  Erdos287.V16Status.balancedSeven_of_factorialEndpoint_and_comparison
    (factorialEndpoint_of_3221 S hQ hDI hdec) hcomp

/-! ## Non-fabrication record

The regrouping identity `Erdos287.Grouping3221.sevenfold_regrouping` and the finite
diagonal bound `Erdos287.Diagonal3221.sourceAssisted_diagonal_finite` are unconditional
theorems and therefore appear as *facts*, not as antecedents, of the compiler.  They do
**not** by themselves produce any bound on the completed value: that is exactly the content
of the open socket. -/

/-- The regrouping used by the compiler is an unconditional identity (restated for the
record). -/
theorem regrouping_is_unconditional {K : Type*} [CommRing K] (om : ℕ → Fin 7 → K) {m : ℕ}
    (hm : m ≠ 0) :
    ∑ t ∈ Erdos287.FactorialEuler.ordFact 7 m, ∏ i, om (t i) i
      = ∑ u ∈ Erdos287.Grouping3221.tuples 4 m,
          (Erdos287.Grouping3221.eta om) (u 0) * (Erdos287.Grouping3221.alpha om) (u 1) *
            (Erdos287.Grouping3221.beta om) (u 2) * (Erdos287.Grouping3221.gamma om) (u 3) :=
  Erdos287.Grouping3221.sevenfold_regrouping om hm

end Compiler3221
end Erdos287
