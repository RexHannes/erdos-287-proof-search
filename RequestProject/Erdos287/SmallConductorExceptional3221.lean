import Mathlib

/-!
# V23, §8–§10 — small-conductor and exceptional-character interfaces, and the
effectivity firewall

`BALANCED7-LOWCOND-EXCEPTIONAL-SPLICE45`

Three things live here, kept strictly apart:

* `SmallConductorNegligible287Input` — the ordinary small-conductor analytic input
  (`r ≤ D = log X`, induced characters mod `q`, the seven SP-2 prime boxes, the Mellin/log
  insertion and the aggregate `q` weighting), with conclusion `O_A(X log^{-A} X)`.
  Metadata cites Siegel–Walfisz / uniform PNT in arithmetic progressions.  **Uninhabited.**
* `ExceptionalCharacterNegligible287Input` — the *separate* possible exceptional real
  character.  Deliberately **not** merged with the ordinary small conductors, and carrying
  an `ineffective` flag that must travel downstream.  **Uninhabited.**
* the effectivity firewall: `BalancedSevenStatusRecord` with the two distinct statuses
  `asymptoticClosed` and `effectiveClosed`, and
  `asymptoticBalancedSeven_not_effectiveAutomatically`, which proves that a well-formed
  record whose exceptional input is ineffective can **not** be effectively closed and
  supplies **no** explicit threshold.

Neither analytic theorem is proved here; per the independent audit
(`OPUS NANC : CASE F — SOURCE-MISSING`) the small-conductor and exceptional physical
sources are not verified, so both interfaces stay uninhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V23LowCond

/-! ## §8  The ordinary small-conductor input -/

/-- **`SmallConductorNegligible287Input`** — `EXTERNAL / UNINHABITED`.

Literal source shape:

```
    primitive conductor r ≤ D = log X;
    characters mod q induced from those primitive characters;
    seven SP-2 prime boxes;
    Mellin / log insertion;
    aggregate q weighting
                    ⇒  total contribution = O_A(X log^{-A} X).
```

Metadata: the analytic engine behind such a bound is Siegel–Walfisz / uniform PNT in
arithmetic progressions.  Nothing of the kind is proved in this repository. -/
structure SmallConductorNegligible287Input
    (X D Aexp Cbound : ℝ) (boxCount : ℕ)
    (moduli conductors : Finset ℕ) (inducedBy : ℕ → ℕ)
    (cellContribution weightFn logInsertion : ℕ → ℝ) (total : ℝ) : Prop where
  /-- The cutoff is the shared `D = log X`. -/
  cutoff_is_log : D = Real.log X
  /-- The scale is nontrivial. -/
  scale_large : 3 ≤ X
  /-- The primitive conductors are genuinely small: `1 ≤ r ≤ D`. -/
  conductor_small : ∀ r ∈ conductors, 1 ≤ r ∧ (r : ℝ) ≤ D
  /-- Each modulus carries a character induced from a primitive one of small conductor. -/
  induced : ∀ q ∈ moduli, inducedBy q ∈ conductors ∧ inducedBy q ∣ q
  /-- The seven SP-2 prime boxes. -/
  seven_boxes : boxCount = 7
  /-- The Mellin / log insertion, cell by cell. -/
  mellin_insertion : ∀ q ∈ moduli, cellContribution q = weightFn q * logInsertion q
  /-- The aggregate `q` weighting assembles the total. -/
  aggregate_weighting : total = ∑ q ∈ moduli, cellContribution q
  /-- The required conclusion. -/
  negligible : |total| ≤ Cbound * X * (Real.log X) ^ (-Aexp)
  /-- A genuine log saving. -/
  saving_positive : 0 < Aexp

/-- **`smallConductorNegligible_is_a_restriction`.**  `LEAN_PROVED`.

Explicit data refute the interface, so it cannot be discharged by generalities. -/
theorem smallConductorNegligible_is_a_restriction :
    ∃ (X D Aexp Cbound : ℝ) (boxCount : ℕ) (moduli conductors : Finset ℕ)
      (inducedBy : ℕ → ℕ) (cellContribution weightFn logInsertion : ℕ → ℝ) (total : ℝ),
      ¬ SmallConductorNegligible287Input X D Aexp Cbound boxCount moduli conductors
        inducedBy cellContribution weightFn logInsertion total := by
  refine ⟨0, 0, 1, 0, 7, ∅, ∅, id, fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_⟩
  intro h
  have := h.scale_large
  norm_num at this

/-! ## §9  The exceptional character input (kept separate) -/

/-- **`ExceptionalCharacterNegligible287Input`** — `EXTERNAL / UNINHABITED`.

The optional primitive real character of conductor `≤ D`, its induced mod-`q` source, the
non-effectivity flag, and the required aggregate bound.  This is deliberately a *separate*
interface from `SmallConductorNegligible287Input`: merging them would silently launder an
ineffective bound into the ordinary channel.

`ineffective` is a parameter of the interface, so the flag is part of the type and travels
downstream with every use. -/
structure ExceptionalCharacterNegligible287Input
    (X D Aexp Cbound : ℝ) (exceptionalConductor : Option ℕ) (moduli : Finset ℕ)
    (inducedBy : ℕ → ℕ) (total : ℝ) (ineffective : Bool) : Prop where
  /-- The cutoff is the shared `D = log X`. -/
  cutoff_is_log : D = Real.log X
  /-- The scale is nontrivial. -/
  scale_large : 3 ≤ X
  /-- If an exceptional character is present, its conductor is `≤ D`. -/
  conductor_small : ∀ r ∈ exceptionalConductor, (r : ℝ) ≤ D
  /-- The mod-`q` sources induced by the exceptional character. -/
  induced : ∀ q ∈ moduli, ∀ r ∈ exceptionalConductor, inducedBy q = r → r ∣ q
  /-- The required aggregate bound. -/
  negligible : |total| ≤ Cbound * X * (Real.log X) ^ (-Aexp)
  /-- A genuine log saving. -/
  saving_positive : 0 < Aexp

/-- **`exceptionalCharacterNegligible_is_a_restriction`.**  `LEAN_PROVED`. -/
theorem exceptionalCharacterNegligible_is_a_restriction :
    ∃ (X D Aexp Cbound : ℝ) (exceptionalConductor : Option ℕ) (moduli : Finset ℕ)
      (inducedBy : ℕ → ℕ) (total : ℝ) (ineffective : Bool),
      ¬ ExceptionalCharacterNegligible287Input X D Aexp Cbound exceptionalConductor moduli
        inducedBy total ineffective := by
  refine ⟨0, 0, 1, 0, none, ∅, id, 0, true, ?_⟩
  intro h
  have := h.scale_large
  norm_num at this

/-! ## §10  The effectivity firewall -/

/-- A Balanced7 closure status record, with the two statuses kept apart. -/
structure BalancedSevenStatusRecord where
  /-- `BalancedSevenAsymptoticClosed`. -/
  asymptoticClosed : Bool
  /-- `BalancedSevenEffectiveClosed`. -/
  effectiveClosed : Bool
  /-- Whether the exceptional-character treatment used is ineffective. -/
  exceptionalIneffective : Bool
  /-- The explicit threshold `M₀`, when one is available. -/
  explicitThreshold : Option ℕ
  deriving DecidableEq, Repr

/-- **`WellFormedStatus`** — the two audit rules a status record must obey:

* effective closure requires an explicit threshold;
* an ineffective exceptional input supplies no explicit threshold. -/
def WellFormedStatus (R : BalancedSevenStatusRecord) : Prop :=
  (R.effectiveClosed = true → R.explicitThreshold ≠ none) ∧
    (R.exceptionalIneffective = true → R.explicitThreshold = none)

/-- **`asymptoticBalancedSeven_not_effectiveAutomatically`.**  `LEAN_PROVED`.

The mandated firewall: whatever the asymptotic status, a well-formed record whose only
exceptional-character treatment is ineffective is **not** effectively closed. -/
theorem asymptoticBalancedSeven_not_effectiveAutomatically
    (R : BalancedSevenStatusRecord) (hw : WellFormedStatus R)
    (hineff : R.exceptionalIneffective = true) :
    R.effectiveClosed = false := by
  by_contra h
  have htrue : R.effectiveClosed = true := by
    cases hb : R.effectiveClosed with
    | false => exact absurd hb h
    | true => rfl
  exact hw.1 htrue (hw.2 hineff)

/-- **`ineffective_supplies_no_threshold`.**  `LEAN_PROVED`.

Gate-2 / effectivity compilers may not read an explicit `M₀` out of the weaker status. -/
theorem ineffective_supplies_no_threshold
    (R : BalancedSevenStatusRecord) (hw : WellFormedStatus R)
    (hineff : R.exceptionalIneffective = true) :
    R.explicitThreshold = none :=
  hw.2 hineff

/-- **`asymptotic_and_effective_are_distinct`.**  `LEAN_PROVED`.

The two statuses genuinely differ: there is a well-formed record that is asymptotically
closed and not effectively closed. -/
theorem asymptotic_and_effective_are_distinct :
    ∃ R : BalancedSevenStatusRecord,
      WellFormedStatus R ∧ R.asymptoticClosed = true ∧ R.effectiveClosed = false := by
  refine ⟨⟨true, false, true, none⟩, ⟨?_, ?_⟩, rfl, rfl⟩
  · intro h; exact absurd h (by simp)
  · intro _; rfl

end V23LowCond
end Erdos287
