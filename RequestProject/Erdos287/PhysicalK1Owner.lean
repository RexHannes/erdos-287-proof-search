import Mathlib
import RequestProject.Erdos287.CentredFrontierTriviality
import RequestProject.Erdos287.HighXConsumerLedger

/-!
# Erdős #287 — the corrected quantitative `k = 1` owner (§68)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.  Nothing here claims Erdős #287.

§62 refuted the recorded `k = 1` frontier targets:

```
FixedConductorCharacterBound      : FALSE  (fixedConductorCharacterBound_unsatisfiable)
FixedConductorCharacterMeanBound  : FALSE  (characterMeanBound_unsatisfiable)
BoundedConductorK1Target          : FALSE  (boundedConductorK1Target_unsatisfiable)
```

and §64 showed that the *qualitative* density-centred replacement carries no analytic
content.  **None of the refuted propositions is reused here, as a hypothesis or otherwise.**

This module states the weakest *quantitative* `k = 1` proposition that the physical owner
ledger actually needs, over the physical hyperbola windows, with the true (bounded) source
weights and the correct density centring:

```
PhysicalK1Budget b :
  ∀ X w A B z,  SourceWeight w → PhysicalWindow X A B →
    | ∑_{1000 < ℓ ≤ 5000} ∑_{s ∈ [A,B)} w s · (K_ℓ(s,z) − mean_ℓ(z)) |  ≤  b · X.
```

Proved here:

* `centredWeighted_full_period_vanishes` — the *density* witness that refuted the old
  pointwise target is annihilated by the centring: over full periods with the constant weight
  the centred physical sum is exactly `0`.  So the new owner is not refuted by the banked
  obstruction.
* `exists_physicalK1_budget` — *some* budget works, with the explicit admissible constant
  `2 ∑_ℓ Kbound ℓ`; hence, exactly as in §64, all the content of the owner sits in the
  **smallness** of `b`, and the node is quantitative.
* `physicalK1Budget_mono` — monotonicity in the budget.
* `physicalK1_consumer_bound` — the deterministic bridge to the high-`X` consumer ledger:
  a budget `b` that fits the ledger transports to the consumer bound with the ledger's own
  available leakage budget.
* `refuted_targets_not_reused` — an explicit record that the three refuted propositions stay
  refuted and are not hypotheses of the new owner.

The proposition `PhysicalK1Budget b` for a *ledger-admissible* `b` is **OPEN**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §68.1  Physical windows and true source weights -/

/-- **True source weights**: the physical source attaches to each window point a weight of
absolute value at most `1` (normalised divisor/Λ-weights). -/
def SourceWeight (w : ℤ → ℚ) : Prop := ∀ s, |w s| ≤ 1

/-- **Physical hyperbola window at scale `X`**: a nonnegative half-open window inside `[0, X]`
which is *long*, i.e. carries at least half the scale.  (Short windows are owned elsewhere in
the ledger; the `k = 1` owner is only ever asked about long physical windows.) -/
def PhysicalWindow (X : ℕ) (A B : ℤ) : Prop :=
  0 ≤ A ∧ A ≤ B ∧ B ≤ (X : ℤ) ∧ (X : ℤ) ≤ 2 * (B - A)

/-- The **density-centred physical window sum** with the true source weights. -/
def centredWeighted (w : ℤ → ℚ) (A B z : ℤ) : ℚ :=
  ∑ ell ∈ conductorRange, ∑ s ∈ Finset.Ico A B, w s * (Kell ell s z - perMean ell z)

/-- **The corrected quantitative `k = 1` owner.**  A budget `b` is admissible when every
physical window sum with true source weights is at most `b · X`. -/
def PhysicalK1Budget (b : ℚ) : Prop :=
  ∀ (X : ℕ) (w : ℤ → ℚ) (A B z : ℤ), SourceWeight w → PhysicalWindow X A B →
    |centredWeighted w A B z| ≤ b * (X : ℚ)

/-- **`physicalK1Budget_mono`.**  `KERNEL-PROVED`. -/
theorem physicalK1Budget_mono {b b' : ℚ} (hbb : b ≤ b') (h : PhysicalK1Budget b) :
    PhysicalK1Budget b' := by
  intro X w A B z hw hwin
  refine (h X w A B z hw hwin).trans ?_
  have hX : (0 : ℚ) ≤ (X : ℚ) := Nat.cast_nonneg X
  exact mul_le_mul_of_nonneg_right hbb hX

/-! ## §68.2  The density obstruction is annihilated by the centring -/

/-- **`centredWeighted_full_period_vanishes`.**  `KERNEL-PROVED`.  With the constant weight,
at the outer point `z = 1`, over `n` complete periods the centred physical sum is exactly
zero.  The long-window witness `returnedKernel_long_window` — which refuted the *uncentred*
pointwise target for every budget — therefore does not refute the corrected owner. -/
theorem centredWeighted_full_period_vanishes (n : ℕ) :
    centredWeighted (fun _ => 1) 0 ((bigPeriod : ℤ) * (n : ℤ)) 1 = 0 := by
  refine Finset.sum_eq_zero fun ell hell => ?_
  rw [conductorRange, Finset.mem_Icc] at hell
  have hmean : perMean ell 1 = meanTerm ell := by
    rw [perMean_one, meanK_eq_meanTerm (by omega)]
  have hcard : (Finset.Ico (0 : ℤ) ((bigPeriod : ℤ) * (n : ℤ))).card
      = ((bigPeriod : ℤ) * (n : ℤ)).toNat := by
    rw [Int.card_Ico, sub_zero]
  have hsplit : ∑ s ∈ Finset.Ico (0 : ℤ) ((bigPeriod : ℤ) * (n : ℤ)),
        (1 : ℚ) * (Kell ell s 1 - perMean ell 1)
      = (∑ s ∈ Finset.Ico (0 : ℤ) ((bigPeriod : ℤ) * (n : ℤ)), Kell ell s 1)
        - ((Finset.Ico (0 : ℤ) ((bigPeriod : ℤ) * (n : ℤ))).card : ℚ) * perMean ell 1 := by
    rw [Finset.sum_congr rfl (fun s _ => one_mul _), Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
  rw [hsplit, Kell_long_window hell.1 hell.2 n, hmean, hcard]
  have htn : (((bigPeriod : ℤ) * (n : ℤ)).toNat : ℚ) = (bigPeriod : ℚ) * (n : ℚ) := by
    have hz : ((bigPeriod : ℤ) * (n : ℤ)) = ((bigPeriod * n : ℕ) : ℤ) := by push_cast; ring
    rw [hz, Int.toNat_natCast]; push_cast; ring
  rw [htn]
  ring

/-! ## §68.3  Some budget works: the owner is a *quantitative* node -/

/-- The explicit admissible constant. -/
def physicalK1TrivialBudget : ℚ := 2 * ∑ ell ∈ conductorRange, Kbound ell

/-- **`exists_physicalK1_budget`.**  `KERNEL-PROVED`.  The corrected owner is satisfiable for
the explicit (very large) constant `2 ∑_ℓ Kbound ℓ`.  All of its analytic content therefore
lies in the *smallness* of the budget: the node is quantitative, exactly as the §64 firewall
requires. -/
theorem exists_physicalK1_budget : PhysicalK1Budget physicalK1TrivialBudget := by
  intro X w A B z hw hwin
  obtain ⟨hA, hAB, hBX, -⟩ := hwin
  have hXnn : (0 : ℚ) ≤ (X : ℚ) := Nat.cast_nonneg X
  have hlen : ((Finset.Ico A B).card : ℚ) ≤ (X : ℚ) := by
    rw [Int.card_Ico]
    have h1 : (B - A).toNat ≤ X := by omega
    exact_mod_cast h1
  have hbound : ∀ ell ∈ conductorRange,
      |∑ s ∈ Finset.Ico A B, w s * (Kell ell s z - perMean ell z)|
        ≤ (X : ℚ) * (2 * Kbound ell) := by
    intro ell hell
    rw [conductorRange, Finset.mem_Icc] at hell
    have hne : ell ≠ 0 := by omega
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hstep : ∀ s ∈ Finset.Ico A B,
        |w s * (Kell ell s z - perMean ell z)| ≤ 2 * Kbound ell := by
      intro s _
      rw [abs_mul]
      have h1 : |w s| ≤ 1 := hw s
      have h2 : |Kell ell s z - perMean ell z| ≤ 2 * Kbound ell := by
        have hA := abs_Kell_le hne s z
        have hB := abs_perMean_le (Nat.pos_of_ne_zero hne) z
        have habs : |Kell ell s z - perMean ell z| ≤ |Kell ell s z| + |perMean ell z| :=
          abs_sub (Kell ell s z) (perMean ell z)
        linarith
      have h3 : (0 : ℚ) ≤ |Kell ell s z - perMean ell z| := abs_nonneg _
      calc |w s| * |Kell ell s z - perMean ell z|
          ≤ 1 * |Kell ell s z - perMean ell z| := by
            exact mul_le_mul_of_nonneg_right h1 h3
        _ = |Kell ell s z - perMean ell z| := one_mul _
        _ ≤ 2 * Kbound ell := h2
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hK : (0 : ℚ) ≤ 2 * Kbound ell := by
      have := Kbound_nonneg ell
      linarith
    exact mul_le_mul_of_nonneg_right hlen hK
  calc |centredWeighted w A B z|
      ≤ ∑ ell ∈ conductorRange,
          |∑ s ∈ Finset.Ico A B, w s * (Kell ell s z - perMean ell z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ell ∈ conductorRange, (X : ℚ) * (2 * Kbound ell) := Finset.sum_le_sum hbound
    _ = physicalK1TrivialBudget * (X : ℚ) := by
        simp only [physicalK1TrivialBudget, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ell _ => by ring

/-! ## §68.4  The deterministic bridge to the high-`X` consumer ledger -/

/-- **`physicalK1_consumer_bound`.**  `KERNEL-PROVED` (deterministic bridge).  If the
corrected owner holds with a budget that fits the high-`X` ledger, then every physical window
sum is bounded by the ledger's own available leakage budget times the scale. -/
theorem physicalK1_consumer_bound {b : ℚ} (L : HighX.Ledger) (hb : PhysicalK1Budget b)
    (hfit : HighX.Fits L b) (X : ℕ) (w : ℤ → ℚ) (A B z : ℤ)
    (hw : SourceWeight w) (hwin : PhysicalWindow X A B) :
    |centredWeighted w A B z| ≤ HighX.availableLeakageBudget L * (X : ℚ) := by
  refine (hb X w A B z hw hwin).trans ?_
  exact mul_le_mul_of_nonneg_right hfit (Nat.cast_nonneg X)


/-! ## §68.6  Narrowing the open node

Two deterministic reductions.  The first splits the owner over conductors, so the open
proposition is a *per-conductor* one.  The second closes the **constant-weight** case
outright: with `w ≡ 1` the centred physical window sum is bounded by the `X`-independent
constant `centredBudget` of §64.  Consequently all the remaining analytic content of the
corrected `k = 1` owner sits in the *non-constant* true source weights. -/

/-- **`physicalK1_of_perConductor`.**  `KERNEL-PROVED` (deterministic reduction).  A
per-conductor budget `c ℓ` for the centred physical window sums gives the aggregate owner
with budget `∑_ℓ c ℓ`. -/
theorem physicalK1_of_perConductor (c : ℕ → ℚ)
    (h : ∀ ell ∈ conductorRange, ∀ (X : ℕ) (w : ℤ → ℚ) (A B z : ℤ), SourceWeight w →
      PhysicalWindow X A B →
        |∑ s ∈ Finset.Ico A B, w s * (Kell ell s z - perMean ell z)| ≤ c ell * (X : ℚ)) :
    PhysicalK1Budget (∑ ell ∈ conductorRange, c ell) := by
  intro X w A B z hw hwin
  calc |centredWeighted w A B z|
      ≤ ∑ ell ∈ conductorRange,
          |∑ s ∈ Finset.Ico A B, w s * (Kell ell s z - perMean ell z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ell ∈ conductorRange, c ell * (X : ℚ) :=
        Finset.sum_le_sum fun ell hell => h ell hell X w A B z hw hwin
    _ = (∑ ell ∈ conductorRange, c ell) * (X : ℚ) := by rw [Finset.sum_mul]

/-- **`constantWeight_centred_bound`.**  `KERNEL-PROVED`.  With the constant weight the
centred physical window sum is bounded by the `X`-independent constant `centredBudget`. -/
theorem constantWeight_centred_bound (A B z : ℤ) (hAB : A ≤ B) :
    |centredWeighted (fun _ => 1) A B z| ≤ centredBudget := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun ell hell => ?_
  rw [conductorRange, Finset.mem_Icc] at hell
  have hpos : 0 < ell := by omega
  have hcard : ((Finset.Ico A B).card : ℚ) = ((B - A : ℤ) : ℚ) := by
    rw [Int.card_Ico]
    have : ((B - A).toNat : ℤ) = B - A := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun x : ℤ => (x : ℚ)) this
  have hrw : ∑ s ∈ Finset.Ico A B, (1 : ℚ) * (Kell ell s z - perMean ell z)
      = (∑ s ∈ Finset.Ico A B, Kell ell s z) - ((B - A : ℤ) : ℚ) * perMean ell z := by
    rw [Finset.sum_congr rfl (fun s _ => one_mul _), Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hcard]
  rw [hrw]
  refine (windowSum_centred_bound hpos A B z hAB).trans ?_
  have hmean := abs_perMean_le hpos z
  have hell0 : (0 : ℚ) ≤ (ell : ℚ) := Nat.cast_nonneg ell
  have : (ell : ℚ) * (Kbound ell + |perMean ell z|)
      ≤ (ell : ℚ) * (Kbound ell + Kbound ell) := by
    refine mul_le_mul_of_nonneg_left ?_ hell0
    linarith
  exact this

/-- **`constantWeight_physicalK1`.**  `KERNEL-PROVED`.  The constant-weight case of the
corrected owner holds with the explicit budget `centredBudget`.  The open content of the
node is therefore exactly the *non-constant* true source weights. -/
theorem constantWeight_physicalK1 (X : ℕ) (A B z : ℤ) (hX : 1 ≤ X)
    (hwin : PhysicalWindow X A B) :
    |centredWeighted (fun _ => 1) A B z| ≤ centredBudget * (X : ℚ) := by
  have hAB : A ≤ B := hwin.2.1
  refine (constantWeight_centred_bound A B z hAB).trans ?_
  have hb : 0 ≤ centredBudget := by
    refine Finset.sum_nonneg fun ell _ => ?_
    have := Kbound_nonneg ell
    have hell0 : (0 : ℚ) ≤ (ell : ℚ) := Nat.cast_nonneg ell
    have : (0 : ℚ) ≤ Kbound ell + Kbound ell := by linarith
    exact mul_nonneg hell0 this
  have hX1 : (1 : ℚ) ≤ (X : ℚ) := by exact_mod_cast hX
  nlinarith

/-! ## §68.5  The refuted propositions are not reused -/

/-- **`refuted_targets_not_reused`.**  `KERNEL-PROVED` bookkeeping.  The three refuted
propositions remain refuted for every budget; the corrected owner above is a different
proposition, and none of them appears as one of its hypotheses. -/
theorem refuted_targets_not_reused (b : ℚ) :
    ¬ FixedConductorCharacterBound b ∧ ¬ FixedConductorCharacterMeanBound b ∧
      ¬ BoundedConductorK1Target b :=
  ⟨fixedConductorCharacterBound_unsatisfiable b, characterMeanBound_unsatisfiable b,
    boundedConductorK1Target_unsatisfiable b⟩

end Effectivity
end Erdos287
