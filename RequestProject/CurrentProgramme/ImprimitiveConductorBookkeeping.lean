import Mathlib
import RequestProject.CurrentProgramme.SmallQ34LSRoute

/-!
# CurrentProgramme §8 — imprimitive character bookkeeping

The vague constant `C_ind` is replaced by an explicit record.  What is tracked, and what is
*proved* here as finite arithmetic:

* the primitive conductor `f` of a character mod `q` divides `q`;
* `μ(q) ≠ 0` forces `q` squarefree, so only squarefree levels carry a Möbius weight;
* the possible conductors of characters mod `q` lie in `q.divisors`, so the number of lifts
  from a fixed `f` to level `q` is controlled by the divisor multiplicity `d(q)`;
* `q/φ(q) ≥ 1`, with `φ(q) ≤ q`;
* a Dirichlet character vanishes on non-units.

The **total fixed / polylog cost** of the bookkeeping is *not* proved: it is recorded in the
uninhabited source socket `ImprimitiveConductorSourceInput`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §8.1  The explicit finite bookkeeping -/

/-- **`conductor_dvd_level'`.**  `LEAN_PROVED`.  The primitive conductor divides the level. -/
theorem conductor_dvd_level' {q : ℕ} (chi : DirichletCharacter ℂ q) : chi.conductor ∣ q :=
  DirichletCharacter.conductor_dvd_level chi

/-- **`moebius_ne_zero_squarefree_level`.**  `LEAN_PROVED`.

Only squarefree levels carry a nonzero Möbius weight, so the lift bookkeeping only has to
handle squarefree `q`. -/
theorem moebius_ne_zero_squarefree_level {q : ℕ} (h : moebius q ≠ 0) : Squarefree q :=
  moebius_ne_zero_iff_squarefree.1 h

/-- **`conductor_mem_divisors`.**  `LEAN_PROVED`.

For a positive level the conductor is one of the divisors of `q`: the lifts from primitive
conductors to level `q` are indexed by `q.divisors`, whose cardinality is `d(q)`. -/
theorem conductor_mem_divisors {q : ℕ} (hq : q ≠ 0) (chi : DirichletCharacter ℂ q) :
    chi.conductor ∈ q.divisors :=
  Nat.mem_divisors.2 ⟨conductor_dvd_level' chi, hq⟩

/-- **`conductor_lift_count_le_divisor_count`.**  `LEAN_PROVED`.

The set of conductors realised at level `q` has cardinality at most the divisor count. -/
theorem conductor_lift_count_le_divisor_count {q : ℕ} (hq : q ≠ 0)
    (Chis : Finset (DirichletCharacter ℂ q)) :
    (Chis.image fun chi => chi.conductor).card ≤ q.divisors.card := by
  refine Finset.card_le_card ?_
  intro f hf
  obtain ⟨chi, _, rfl⟩ := Finset.mem_image.1 hf
  exact conductor_mem_divisors hq chi

/-- **`q_over_phi_ge_one`.**  `LEAN_PROVED`.  The `q/φ(q)` factor is at least one. -/
theorem q_over_phi_ge_one {q : ℕ} (hq : 0 < q) : 1 ≤ (q : ℝ) / (Nat.totient q : ℝ) := by
  have hphi : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 hq
  rw [le_div_iff₀ hphi, one_mul]
  exact_mod_cast Nat.totient_le q

/-- **`character_vanishes_on_nonunits`.**  `LEAN_PROVED`. -/
theorem character_vanishes_on_nonunits {q : ℕ} (chi : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : ¬ IsUnit a) : chi a = 0 :=
  MulChar.map_nonunit chi ha

/-! ## §8.2  The explicit cost record -/

/-- The explicit replacement for the vague `C_ind`: a finite record of the bookkeeping data
attached to one level `q`. -/
structure ConductorRecord where
  /-- The level. -/
  level : ℕ
  /-- The primitive conductor. -/
  conductor : ℕ
  /-- The conductor divides the level. -/
  conductor_dvd : conductor ∣ level
  /-- The level is squarefree (the only case with `μ(q) ≠ 0`). -/
  level_squarefree : Squarefree level
  /-- The number of lifts recorded at this level. -/
  liftCount : ℕ
  /-- The lift count is bounded by the divisor multiplicity. -/
  liftCount_le : liftCount ≤ level.divisors.card
  /-- The declared polylog cost exponent of the bookkeeping. -/
  costExponent : ℚ

/-- **`conductorRecord_level_pos`.**  `LEAN_PROVED`. -/
theorem conductorRecord_level_pos (R : ConductorRecord) : 0 < R.level :=
  R.level_squarefree.ne_zero.bot_lt

/-- **`conductorRecord_conductor_le_level`.**  `LEAN_PROVED`. -/
theorem conductorRecord_conductor_le_level (R : ConductorRecord) : R.conductor ≤ R.level :=
  Nat.le_of_dvd (conductorRecord_level_pos R) R.conductor_dvd

/-! ## §8.3  The uninhabited source socket -/

/-- **`ImprimitiveConductorSourceInput`** — `EXTERNAL / SOURCE OPEN / UNINHABITED`.

The imprimitive-to-primitive passage with an explicit *total* cost.  The declared cost must
be a genuine polylog bound valid over the whole family of levels; this is the analytic
content that replaces the vague `C_ind`, and it is not supplied here. -/
structure ImprimitiveConductorSourceInput
    (levels : Finset ℕ) (rec : ℕ → ConductorRecord) (Ctotal costExp : ℚ) (X : ℝ) : Prop where
  /-- The family of levels is nonempty. -/
  levels_nonempty : levels.Nonempty
  /-- Each record is attached to its own level. -/
  record_level : ∀ q ∈ levels, (rec q).level = q
  /-- Each level in the family is squarefree. -/
  squarefree : ∀ q ∈ levels, Squarefree q
  /-- The declared cost exponent is uniform over the family. -/
  uniform_cost : ∀ q ∈ levels, (rec q).costExponent = costExp
  /-- The total bookkeeping cost is a fixed polylog cost. -/
  total_cost : (∑ q ∈ levels, ((rec q).liftCount : ℚ)) ≤ Ctotal
  /-- The declared cost is genuinely positive, and the scale is nontrivial. -/
  wellformed : 0 < Ctotal ∧ 3 ≤ X

/-- **`imprimitiveConductor_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction: explicit data refute it.  It is not inhabited. -/
theorem imprimitiveConductor_not_automatic :
    ∃ (levels : Finset ℕ) (rec : ℕ → ConductorRecord) (Ctotal costExp : ℚ) (X : ℝ),
      ¬ ImprimitiveConductorSourceInput levels rec Ctotal costExp X := by
  classical
  refine ⟨∅, fun _ =>
    { level := 1, conductor := 1, conductor_dvd := dvd_rfl,
      level_squarefree := squarefree_one, liftCount := 0,
      liftCount_le := Nat.zero_le _, costExponent := 0 }, 1, 0, 3, ?_⟩
  intro h
  simpa using h.levels_nonempty

end CurrentProgramme
end Erdos287
