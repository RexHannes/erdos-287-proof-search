import Mathlib
import RequestProject.Erdos287.MovingPhaseProvider3221
import RequestProject.Erdos287.BalancedSeven3221Compiler

/-!
# V18, Phase G — the factorial-endpoint source adapter

`FACTORIAL-ENDPOINT-3221-SOURCE-ADAPTER45 : SOURCE_OPEN / UNINHABITED`
`3221-ENDPOINT-SMALLZ-COMPILER45 : CONDITIONAL_COMPILER (Lean-proved)`

The strongest purely logical compiler justified by the types that actually exist in this
repository is

```
pinned 3221 normal form           (SOURCE_BLOCKED, never inhabited)
  + per-level small-Z input       (OPEN_ANALYTIC, never inhabited)
  + endpoint source adapter       (SOURCE_OPEN,  never inhabited)
      ⇒ FactorialOmega7SignedEndpoint          (V16 interface)

  + MuLogComparisonLowCondMatch   (SOURCE_BLOCKED, never inhabited)
      ⇒ BalancedSevenPacketInput               (V16 compiler, reused unchanged)
```

The exact factorial `1+2+2+2` regrouping (`Erdos287.Grouping3221.sevenfold_regrouping`) and
the finite diagonal/off-diagonal packages are unconditional theorems and therefore enter as
*facts*, not as antecedents.

The V16 endpoint type speaks about a real endpoint value `S_fac`; the 3221 child produces a
complex level-decomposed value.  That gap is **not** fabricated: it is carried by the
explicit `SOURCE_OPEN` adapter below, whose fields are concrete inequalities.  Nothing in
this file inhabits any analytic or source antecedent, so no unconditional conclusion is
obtained anywhere, and `BALANCED7` stays `OPEN`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace EndpointAdapter3221

open Erdos287.DI3221
open Erdos287.NormalForm3221
open Erdos287.Phase3221
open Erdos287.Compiler3221

variable {S : BalancedSeven3221CompletedSource}

/-- **`FACTORIAL-ENDPOINT-3221-SOURCE-ADAPTER45` — `SOURCE_OPEN`, never inhabited.**

The data missing between the pinned 3221 normal form and the V16 factorial endpoint:

* the endpoint value is dominated by the source parent value up to the routed error, and
  the analytic target plus routed errors fits inside the admitted budget `E`
  (this is the V17 `Endpoint3221Decomposition`, reused, not redefined);
* the level count of the pinned normal form together with the per-level target fits inside
  the same analytic target — the *aggregation* budget, which is where a genuine levelwise
  provider would have to pay for the number of levels. -/
structure FactorialEndpoint3221SourceAdapter (F : BalancedSeven3221NormalForm S)
    (X eta levelTarget Sfac E : ℝ) : Prop where
  /-- The V17 endpoint decomposition, reused unchanged. -/
  decomposition : Endpoint3221Decomposition S X eta Sfac E
  /-- The level-count budget `#R · levelTarget ≤ X^{39/35−η}`. -/
  levelBudget : (F.Rbox.card : ℝ) * levelTarget ≤ X ^ ((39 / 35 : ℝ) - eta)
  /-- A fixed positive saving. -/
  eta_pos : 0 < eta

/-- **The small-`Z` → factorial endpoint compiler.**  `PROVED_COMPILER / CONDITIONAL`.

Pinned normal form + per-level small-`Z` analytic input + endpoint source adapter
⇒ the V16 `FactorialOmega7SignedEndpoint`.  Every antecedent is uninhabited, so this
theorem inhabits nothing. -/
theorem factorialEndpoint_of_smallZ {F : BalancedSeven3221NormalForm S}
    {X Q eta levelTarget Sfac E : ℝ}
    (hQ : Q = X ^ (3 / 5 : ℝ))
    (hin : PerLevelPhaseSmallZ3221Input F X levelTarget)
    (hadapt : FactorialEndpoint3221SourceAdapter F X eta levelTarget Sfac E) :
    Erdos287.V16Status.FactorialOmega7SignedEndpoint X Q Sfac E :=
  factorialEndpoint_of_3221 S hQ
    (diKuznetsov_of_perLevelSmallZ hin hadapt.eta_pos hadapt.levelBudget)
    hadapt.decomposition

/-- **The full small-`Z` → Balanced7 chain.**  `CONDITIONAL_COMPILER`.

The second step is the already-banked V16 implication, reused through the V17 compiler; it
is not duplicated here.  The comparison antecedent stays source-blocked and uninhabited,
and the two error channels stay separate (`E + err`). -/
theorem balancedSeven_of_smallZ {F : BalancedSeven3221NormalForm S}
    {X Q eta levelTarget Sfac Sphys E err : ℝ}
    (hQ : Q = X ^ (3 / 5 : ℝ))
    (hin : PerLevelPhaseSmallZ3221Input F X levelTarget)
    (hadapt : FactorialEndpoint3221SourceAdapter F X eta levelTarget Sfac E)
    (hcomp : Erdos287.V15Status.MuLogComparisonLowCondMatch X Sphys Sfac err) :
    Erdos287.V16Status.BalancedSevenPacketInput X Sphys (E + err) :=
  balancedSeven_of_3221 S hQ
    (diKuznetsov_of_perLevelSmallZ hin hadapt.eta_pos hadapt.levelBudget)
    hadapt.decomposition hcomp

/-! ## Firewall: the open interfaces are not free

Each of the three open inputs is a genuine restriction on its data — none of them is
satisfied automatically — so the compilers above cannot be turned into unconditional
statements by picking convenient parameters. -/

/-- The factorial endpoint interface is **not** automatically satisfiable: for suitable
data it is false. -/
theorem endpoint_not_automatic :
    ∃ X Q Sfac E : ℝ, ¬ Erdos287.V16Status.FactorialOmega7SignedEndpoint X Q Sfac E := by
  refine ⟨2, 2 ^ (3 / 5 : ℝ), 1, 0, ?_⟩
  intro h
  have := h.bound
  rw [abs_one] at this
  norm_num at this

/-- The comparison interface is **not** automatically satisfiable either: it carries real
content, so no amount of polarization linearity discharges it by itself. -/
theorem comparison_not_automatic :
    ∃ X hard model err : ℝ, 1 < X ∧
      ¬ Erdos287.V15Status.MuLogComparisonLowCondMatch X hard model err := by
  refine ⟨2, 0, 1, 0, by norm_num, ?_⟩
  intro h
  have := h.matched
  norm_num at this

/-- The per-level small-`Z` interface is **not** automatically satisfiable: a nonempty
level box with a level slice exceeding the target refutes it. -/
theorem perLevelSmallZ_not_automatic {F : BalancedSeven3221NormalForm S}
    {X levelTarget : ℝ} {r : ℕ} (hr : r ∈ F.Rbox)
    (hbig : levelTarget < ‖levelValue F r‖) :
    ¬ PerLevelPhaseSmallZ3221Input F X levelTarget := by
  intro h
  exact absurd (h.levelBound r hr) (not_le.mpr hbig)

end EndpointAdapter3221
end Erdos287
