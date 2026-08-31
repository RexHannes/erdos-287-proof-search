import Mathlib
import RequestProject.CurrentProgramme.ShortLiftLocalProfile
import RequestProject.CurrentProgramme.PrimitiveFareyNearCollision

/-!
# The current source socket — Erdős #287, PRIMITIVE-LOCALPROFILE Δ, §F

This module defines the **local-profile primitive-conductor configuration** that the
current frontier

```
287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45
```

is stated over, and states — but does **not** inhabit — the corresponding analytic input
`PrimitiveLocalProfileGramInput`.

The configuration literally retains

* the `π`-side weight, the shift `s`, the dyadic parameter `τ`;
* the conductor `g`, a **primitive** residue `t` (`1 ≤ t ≤ g`, `gcd(t,g) = 1`);
* the friable variable `a` and the Möbius variable `b`;
* the local profile `mProfile(g, b, Q/g)` — the very object of §C, not a substitute;
* `μ(g)`;
* smooth weights (bounded by `1`).

The analytic target is `X log^{-3-η} X`; it is recorded as the shape of the bound in the
socket, never proved.  Only the trivial conditional consumer
`primitiveLocalProfileGram_compiler` uses the socket, and
`primitiveLocalProfileGram_not_automatic` exhibits explicit data refuting it, so the socket
is neither vacuous nor automatic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace PrimitiveLocalProfile

open Erdos287.ShortLift

/-! ## §F.1  The configuration -/

/-- The retained local-profile primitive-conductor configuration. -/
structure PrimitiveConductorConfig where
  /-- The conductor scale `Q`. -/
  Q : ℕ
  /-- The conductor `g`. -/
  g : ℕ
  /-- The primitive residue `t`. -/
  t : ℕ
  /-- The Möbius variable `b`. -/
  b : ℕ
  /-- The friable variable `a`. -/
  a : ℕ
  /-- The shift `s`. -/
  s : ℤ
  /-- The dyadic parameter `τ`. -/
  tau : ℚ
  /-- The `π`-side weight. -/
  piWeight : ℕ → ℝ
  /-- The smooth weight. -/
  smoothWeight : ℝ → ℝ
  /-- The profile weight `Ψ`. -/
  Psi : ℚ → ℚ

namespace PrimitiveConductorConfig

variable (c : PrimitiveConductorConfig)

/-- The local profile carried by the configuration: literally `mProfile(g, b, Q/g)` of §C,
truncated at the same length `Q/g`. -/
def localProfile : ℚ := mProfile c.g c.b (c.Q / c.g) c.Psi (c.Q / c.g)

/-- `μ(g)` as carried by the configuration. -/
def moebiusG : ℤ := moebius c.g

/-- Validity of a configuration: primitivity of `t`, friability of `a`, squarefree conductor,
and bounded smooth weight. -/
structure Valid : Prop where
  /-- The conductor is positive. -/
  g_pos : 0 < c.g
  /-- The conductor is squarefree (the sector of §A.3). -/
  g_squarefree : Squarefree c.g
  /-- `t` lies in the fundamental box. -/
  t_range : 1 ≤ c.t ∧ c.t ≤ c.g
  /-- `t` is **primitive** modulo `g`. -/
  t_primitive : Nat.Coprime c.t c.g
  /-- The Möbius variable is positive. -/
  b_pos : 0 < c.b
  /-- `a` is friable at the conductor scale `Q`. -/
  a_friable : ∀ p ∈ c.a.primeFactors, p ≤ c.Q
  /-- The smooth weight is bounded by `1`. -/
  smooth_bounded : ∀ x : ℝ, |c.smoothWeight x| ≤ 1

end PrimitiveConductorConfig

/-- The socket consumes the *repository's* local profile, by definition — no substitute
object is introduced. -/
theorem localProfile_is_the_repository_mProfile (c : PrimitiveConductorConfig) :
    c.localProfile = mProfile c.g c.b (c.Q / c.g) c.Psi (c.Q / c.g) := rfl

/-- A valid configuration exists, so the socket below is not vacuously satisfiable by an
empty configuration class. -/
theorem exists_valid_config : ∃ c : PrimitiveConductorConfig, c.Valid := by
  refine ⟨⟨2, 1, 1, 1, 1, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩
  refine ⟨by norm_num, squarefree_one, ⟨le_refl 1, le_refl 1⟩, ?_, by norm_num,
    ?_, ?_⟩
  · simp [Nat.Coprime]
  · intro p hp
    simp at hp
  · intro x
    simp

/-! ## §F.2  The analytic socket — stated, never inhabited -/

/-- **`PrimitiveLocalProfileGramInput` — ANALYTIC / UNINHABITED.**

The Gram-side analytic input of `287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45`: uniformly
over valid local-profile primitive-conductor configurations, the Gram functional obeys the
target bound

```
|Gram(c)| ≤ C · X · (log X)^{-3-η}.
```

This is an analytic statement.  It is **not** proved anywhere in this repository and this
structure has **no inhabitant**. -/
structure PrimitiveLocalProfileGramInput (X eta C : ℝ)
    (gram : PrimitiveConductorConfig → ℝ) : Prop where
  /-- The scale is in the admissible range. -/
  X_large : 2 ≤ X
  /-- The saving exponent is a genuine gain beyond `log^{-3}`. -/
  eta_pos : 0 < eta
  /-- The implied constant is explicit and nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The analytic target itself. -/
  gram_bound : ∀ c : PrimitiveConductorConfig, c.Valid →
    |gram c| ≤ C * X * (Real.log X) ^ (-(3 + eta))

/-- The conclusion the socket would deliver, for a single configuration. -/
def PrimitiveLocalProfileGramConclusion (X eta C : ℝ) (value : ℝ) : Prop :=
  |value| ≤ C * X * (Real.log X) ^ (-(3 + eta))

/-- **Conditional consumer.**  `CONDITIONAL / LEAN_PROVED`.  Nothing unconditional is
obtained: the antecedent is uninhabited. -/
theorem primitiveLocalProfileGram_compiler {X eta C : ℝ}
    {gram : PrimitiveConductorConfig → ℝ}
    (inp : PrimitiveLocalProfileGramInput X eta C gram)
    (c : PrimitiveConductorConfig) (hc : c.Valid) :
    PrimitiveLocalProfileGramConclusion X eta C (gram c) :=
  inp.gram_bound c hc

/-- **`primitiveLocalProfileGram_not_automatic`.**  `LEAN_PROVED`.

Explicit data refuting the socket: with `C = 0` and a Gram functional of constant value `1`
the target bound fails on the valid configuration of `exists_valid_config`.  Hence the socket
is a real hypothesis, and `287-K0-SP2-DET1-PRIMITIVE-LOCALPROFILE-GRAM45` is `ANALYTIC OPEN;
UNINHABITED`. -/
theorem primitiveLocalProfileGram_not_automatic :
    ∃ (X eta C : ℝ) (gram : PrimitiveConductorConfig → ℝ),
      ¬ PrimitiveLocalProfileGramInput X eta C gram := by
  refine ⟨2, 1, 0, fun _ => 1, ?_⟩
  intro h
  obtain ⟨c, hc⟩ := exists_valid_config
  have hb := h.gram_bound c hc
  simp at hb
  linarith [hb]

/-- The analytic target of the frontier: the exponent `-(3+η)` is strictly beyond `log^{-3}`.
This is bookkeeping about the *shape* of the target, not a proof of it. -/
theorem analytic_target_exponent {eta : ℝ} (h : 0 < eta) : -(3 + eta) < -3 := by linarith

end PrimitiveLocalProfile
end Erdos287
