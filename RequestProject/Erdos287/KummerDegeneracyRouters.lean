import RequestProject.Erdos287.KummerRootStabilizer
import RequestProject.Erdos287.KummerWeilInterface

/-!
# Degeneracy routers for the quadratic-Kummer packet (V12, Part F)

Part F asks that the degeneracy strata of the Kummer backend be *named as predicates* and
that generic packets be proved disjoint from them, rather than dismissed in prose.  This
file does exactly that, for the strata that have a formal counterpart in this project:

| Router | Predicate here | Formal status |
| --- | --- | --- |
| repeated root / zero discriminant | `RepeatedRootStratum` | routed (finite) |
| degenerate leading coefficient | `DegenerateLeadStratum` | routed (finite) |
| nonunit scaling (`n ≡ 0`) | `NonUnitStratum` | routed (finite) |
| collision / root-stabilizer (`n₂ = ±n₁`) | `CollisionStratum` | routed (finite) |

The remaining V12 routers — the *isolated pure multiplicative-character mode*, the
*principal / zero mode*, and the *conductor-loss* stratum — have **no definition anywhere
in this repository** (no `H8`/`H9` audit object, no principal-character mode, no
conductor bookkeeping exists here).  They are therefore reported SOURCE BLOCKED in the
run report and are deliberately *not* invented here.

## Main results

* `generic_not_repeatedRoot`, `generic_not_degenerateLead`, `generic_not_nonUnit`,
  `generic_not_collision` — a generic packet lies in none of the four strata;
* `generic_disjoint_strata` — the same statement in one conjunction;
* `generic_not_square` — the analytic payoff: a generic packet's scaled product is not a
  square, so it is not in the exceptional set of the correlation interface;
* `generic_not_pmExceptional` — the same in the `pmExceptional` language of the Weil
  interface.
-/

open Polynomial

namespace Erdos287
namespace Kummer

variable {K : Type*} [Field K]

/-! ## The strata -/

/-- Repeated-root sector: the discriminant vanishes. -/
def RepeatedRootStratum (a b c : K) : Prop := b ^ 2 - 4 * a * c = 0

/-- Degenerate leading coefficient: the "quadratic" is not quadratic. -/
def DegenerateLeadStratum (a : K) : Prop := a = 0

/-- Nonunit scaling: one of the two scalings vanishes (i.e. `n ≡ 0 mod p`). -/
def NonUnitStratum (n₁ n₂ : K) : Prop := n₁ = 0 ∨ n₂ = 0

/-- Collision / root-stabilizer stratum: the two scalings differ by an element of the
stabilizer of the unordered root pair, which by `quadratic_scaling_square_criterion` is
`{±1}`. -/
def CollisionStratum (n₁ n₂ : K) : Prop := n₂ = n₁ ∨ n₂ = -n₁

/-- A **generic packet**: honest quadratic, nonzero discriminant, unit scalings, and
scalings outside the stabilizer. -/
def GenericPacket (a b c n₁ n₂ : K) : Prop :=
  a ≠ 0 ∧ b ^ 2 - 4 * a * c ≠ 0 ∧ n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ ¬ CollisionStratum n₁ n₂

/-! ## Routing: generic packets avoid every formalized stratum -/

theorem generic_not_repeatedRoot {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ RepeatedRootStratum a b c := h.2.1

theorem generic_not_degenerateLead {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ DegenerateLeadStratum a := h.1

theorem generic_not_nonUnit {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ NonUnitStratum n₁ n₂ := by
  rintro (h0 | h0)
  · exact h.2.2.1 h0
  · exact h.2.2.2.1 h0

theorem generic_not_collision {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ CollisionStratum n₁ n₂ := h.2.2.2.2

/-- **Disjointness from all formalized degeneracy strata**, in one statement. -/
theorem generic_disjoint_strata {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ RepeatedRootStratum a b c ∧ ¬ DegenerateLeadStratum a ∧
      ¬ NonUnitStratum n₁ n₂ ∧ ¬ CollisionStratum n₁ n₂ :=
  ⟨generic_not_repeatedRoot h, generic_not_degenerateLead h,
    generic_not_nonUnit h, generic_not_collision h⟩

/-- **Analytic payoff of the routing.**  For a generic packet the scaled product is not a
square polynomial — the nondegeneracy hypothesis under which the completion bound is
expected to hold. -/
theorem generic_not_square {a b c n₁ n₂ : K} (h : GenericPacket a b c n₁ n₂) :
    ¬ ∃ G : K[X],
        quadPoly (a * n₁ ^ 2) (b * n₁) c * quadPoly (a * n₂ ^ 2) (b * n₂) c = G ^ 2 := by
  rintro ⟨G, hG⟩
  exact h.2.2.2.2 (quadratic_scaling_square_criterion h.1 h.2.1 h.2.2.1 h.2.2.2.1 hG)

/-- The routing in the language of the Weil interface: a generic packet's second scaling
is not in the exceptional set `pmExceptional`. -/
theorem generic_not_pmExceptional {a b c n₁ n₂ : K} [DecidableEq K] {In : Finset K}
    (h : GenericPacket a b c n₁ n₂) :
    n₂ ∉ pmExceptional In n₁ := by
  intro hmem
  have : n₂ = n₁ ∨ n₂ = -n₁ := by
    have := Finset.mem_filter.1 hmem
    simpa using this.2
  exact h.2.2.2.2 this

/-- The repeated-root router is *not* vacuous: in the excluded sector the product really
is a square for every pair of scalings (V11 `repeated_root_scaling_square`), so the
discriminant condition of `GenericPacket` cannot be dropped. -/
theorem repeatedRoot_router_nonvacuous (n₁ n₂ : K) :
    RepeatedRootStratum (1 : K) 0 0 ∧
      quadPoly (1 * n₁ ^ 2) (0 * n₁) 0 * quadPoly (1 * n₂ ^ 2) (0 * n₂) 0
        = (C (n₁ * n₂) * X ^ 2) ^ 2 :=
  ⟨by simp [RepeatedRootStratum], repeated_root_scaling_square n₁ n₂⟩

end Kummer
end Erdos287
