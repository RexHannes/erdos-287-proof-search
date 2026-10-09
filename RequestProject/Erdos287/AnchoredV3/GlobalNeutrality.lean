import Mathlib

/-!
# Anchored V3 — global multiplier neutrality

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Append-only V3 layer.  Anchored V2 is frozen: nothing here edits, re-proves, weakens or
reinterprets a V2 statement, and nothing here extends the certified finite frontier.

This module fixes the correction to the earlier terminal model.  For row data with row moduli
`m r`, row increments `Δ r` and integer multiplier-prime components `comp r ℓ` we distinguish

* `RowwiseNeutral` : every row individually kills every multiplier-prime component;
* `GlobalNeutral`  : only the *sum over rows* of the components vanishes;
* `ExactTerminalCompletion` : `S₀ + ∑ r, Δ r = 1` on the fixed protected terminal sites.

We prove `RowwiseNeutral → GlobalNeutral`, and we exhibit an explicit finite witness of
`GlobalNeutral ∧ ¬ RowwiseNeutral`.  The converse implication is deliberately **not** proved:
it is false, as the witness shows.  Consequently the old rowwise-neutral compiler is a *valid
sufficient subspace* of the legal terminal search space, but not the complete one.

Finally we record the exact `lcm` decomposition `D = lcm_r (m r)` and, under an explicit
coprimality hypothesis, `D = D_core * U_mult`.  No asymptotic estimate (e.g. `log U_mult = O(R)`)
is stated or used.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- Finite row data of a terminal model: a finite set of rows, a modulus and a rational
increment per row, a finite set of multiplier primes, and the integer component of each row's
increment at each multiplier prime. -/
structure RowData where
  /-- the finite set of rows -/
  rows : Finset ℕ
  /-- the modulus of each row -/
  m : ℕ → ℕ
  /-- the finite set of multiplier primes -/
  primes : Finset ℕ
  /-- the integer multiplier-prime component contributed by a row -/
  comp : ℕ → ℕ → ℤ
  /-- the rational increment of a row -/
  incr : ℕ → ℚ

namespace RowData

variable (d : RowData)

/-- **Rowwise neutrality**: each row increment individually cancels every multiplier-prime
component assigned to that row. -/
def RowwiseNeutral : Prop := ∀ r ∈ d.rows, ∀ ℓ ∈ d.primes, d.comp r ℓ = 0

/-- **Global neutrality**: the sum of the row increments cancels every multiplier-prime
component, without any per-row requirement. -/
def GlobalNeutral : Prop := ∀ ℓ ∈ d.primes, ∑ r ∈ d.rows, d.comp r ℓ = 0

/-- **Exact terminal completion**: the baseline plus the sum of all row increments is `1`. -/
def ExactTerminalCompletion (S₀ : ℚ) : Prop := S₀ + ∑ r ∈ d.rows, d.incr r = 1

/-- The global modulus `D = lcm_r (m r)`. -/
def modulusLcm : ℕ := d.rows.lcm d.m

end RowData

/-- **Rowwise neutrality implies global neutrality.**  (The converse is false; see
`exists_globalNeutral_not_rowwiseNeutral`.) -/
theorem globalNeutral_of_rowwiseNeutral {d : RowData} (h : d.RowwiseNeutral) :
    d.GlobalNeutral := by
  intro ℓ hℓ
  refine Finset.sum_eq_zero ?_
  intro r hr
  exact h r hr ℓ hℓ

/-- The explicit two-row finite witness: two rows whose components at the multiplier prime `2`
are `+1` and `−1`. -/
def witnessData : RowData where
  rows := {0, 1}
  m := fun _ => 1
  primes := {2}
  comp := fun r _ => if r = 0 then 1 else if r = 1 then -1 else 0
  incr := fun _ => 0

theorem witnessData_globalNeutral : witnessData.GlobalNeutral := by
  intro ℓ _
  simp [witnessData]

theorem witnessData_not_rowwiseNeutral : ¬ witnessData.RowwiseNeutral := by
  intro h
  have h0 : witnessData.comp 0 2 = 0 := h 0 (by simp [witnessData]) 2 (by simp [witnessData])
  simp [witnessData] at h0

/-- **The legal terminal search space is strictly larger than the rowwise-neutral subspace.** -/
theorem exists_globalNeutral_not_rowwiseNeutral :
    ∃ d : RowData, d.GlobalNeutral ∧ ¬ d.RowwiseNeutral :=
  ⟨witnessData, witnessData_globalNeutral, witnessData_not_rowwiseNeutral⟩

/-- **The old compiler is sound but incomplete.**  Rowwise neutrality is a sufficient condition
for global neutrality, and it is not a necessary one. -/
theorem rowwise_sufficient_not_necessary :
    (∀ d : RowData, d.RowwiseNeutral → d.GlobalNeutral) ∧
      ∃ d : RowData, d.GlobalNeutral ∧ ¬ d.RowwiseNeutral :=
  ⟨fun _ h => globalNeutral_of_rowwiseNeutral h, exists_globalNeutral_not_rowwiseNeutral⟩

/-- Rowwise-neutral *exact* completions form a subset of the globally neutral exact
completions on the same bank. -/
theorem exact_rowwise_subset_global (S₀ : ℚ) :
    {d : RowData | d.RowwiseNeutral ∧ d.ExactTerminalCompletion S₀} ⊆
      {d : RowData | d.GlobalNeutral ∧ d.ExactTerminalCompletion S₀} := by
  rintro d ⟨h1, h2⟩
  exact ⟨globalNeutral_of_rowwiseNeutral h1, h2⟩

section LcmDecomposition

variable {m : ℕ → ℕ}

/-- The global modulus splits over a partition of the rows into a core part and a multiplier
part. -/
theorem lcm_union (core mult : Finset ℕ) :
    (core ∪ mult).lcm m = Nat.lcm (core.lcm m) (mult.lcm m) :=
  Finset.lcm_union

/-- **Exact `D = D_core * U_mult` decomposition** under the explicit coprimality hypothesis. -/
theorem modulus_eq_core_mul_mult (core mult : Finset ℕ)
    (hcop : Nat.Coprime (core.lcm m) (mult.lcm m)) :
    (core ∪ mult).lcm m = core.lcm m * mult.lcm m := by
  rw [lcm_union]
  exact Nat.Coprime.lcm_eq_mul hcop

/-- Every row modulus divides the global modulus. -/
theorem dvd_modulusLcm {d : RowData} {r : ℕ} (hr : r ∈ d.rows) : d.m r ∣ d.modulusLcm :=
  Finset.dvd_lcm hr

end LcmDecomposition

end AnchoredV3
end Erdos287
