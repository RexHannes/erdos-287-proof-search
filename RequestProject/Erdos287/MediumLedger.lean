import Mathlib
import RequestProject.Erdos287.AllComplement

/-!
# Erdős #287 effectivity — full-vs-medium source typing and the ledger firewall (§7, §8)

```
FULL-vs-MEDIUM TYPING   : KERNEL-PROVED
INCREMENTAL LEDGER TYPE : KERNEL-PROVED
```

With the medium cut `K0 = 31`,

    Θ_{K0,d}(n) = ∑_{k ∣ n, k > K0, 2∤k, (k,d)=1} β(k),
    Π_d(Y)      = ∑_{K0 < k ≤ Y, (k,2d)=1} β(k)/k,

the **medium-only** residual source.  The full all-complement chart is
`∑_{k ∣ n, (k,d)=1} β(k)` (§3), and the simple coefficient `B(w) − B1` belongs to
*that* chart: `mediumChart_ne_fullChart` and `simpleCoefficient_not_medium` show
the two are genuinely different objects already at `d = 1`, `n = 3`.

§8 provides the two ledger **types**.  There is deliberately no coercion from a
full-replacement estimate into an `IncrementalLedger`: `no_naive_full_insertion`
proves that no incremental ledger can carry a full estimate on the same books
unless the removed charges sum to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §7  The medium cut and the medium chart -/

/-- The medium cut. -/
def K0 : ℕ := 31

/-- `Θ_{K0,d}(n) = ∑_{k ∣ n, k > K0, 2∤k, (k,d)=1} β(k)` — the medium-only discrete chart. -/
def Theta (d n : ℕ) : ℚ :=
  ∑ k ∈ n.divisors with (K0 < k ∧ ¬ (2 ∣ k) ∧ Nat.Coprime k d), beta k

/-- `Π_d(Y) = ∑_{K0 < k ≤ Y, (k,2d)=1} β(k)/k` — the medium-only continuous chart. -/
def Pimed (d Y : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc (K0 + 1) Y with (¬ (2 ∣ k) ∧ Nat.Coprime k d), beta k / (k : ℚ)

/-- The **full** all-complement chart of §3. -/
def fullChart (d n : ℕ) : ℚ := ∑ k ∈ n.divisors, betaCop d k

@[simp] lemma fullChart_one_three : fullChart 1 3 = 2 := by
  have h : (3 : ℕ).divisors = {1, 3} := by decide
  rw [fullChart, h]
  norm_num [betaCop, beta_prime (by norm_num : Nat.Prime 3) (by norm_num)]

@[simp] lemma Theta_one_three : Theta 1 3 = 0 := by
  have h : (3 : ℕ).divisors = {1, 3} := by decide
  rw [Theta, h]
  norm_num [K0, Finset.filter_insert, Finset.filter_singleton]

/-- **`mediumChart_ne_fullChart`.**  `KERNEL-PROVED`.  The medium-only chart is not the
full all-complement chart. -/
theorem mediumChart_ne_fullChart : Theta 1 3 ≠ fullChart 1 3 := by
  rw [Theta_one_three, fullChart_one_three]; norm_num

/-- **`simpleCoefficient_not_medium`.**  `KERNEL-PROVED`.  The simple coefficient
`B(d·n) − B1` is produced by the **full** all-complement chart, not by the medium-only
residual: at `d = 1`, `n = 3` the medium chart contributes `0` while the coefficient is
`B1 ≠ 0`. -/
theorem simpleCoefficient_not_medium (B1 : ℚ) (hB1 : B1 ≠ 0) :
    B B1 1 * Theta 1 3 ≠ B B1 (1 * 3) - B1 := by
  have hfull : B B1 1 * fullChart 1 3 = B B1 (1 * 3) :=
    allComplement_discrete B1 (by norm_num) (by norm_num)
  rw [Theta_one_three, mul_zero, ← hfull, fullChart_one_three, B_one]
  intro h
  exact hB1 (by linarith)

/-! ## §8  The ledger-type firewall -/

/-- The source type of a charge: a full all-complement estimate, or a medium-only residual. -/
inductive ChargeSource
  | full
  | medium
  deriving DecidableEq, Repr

/-- An **incremental** ledger: the previously certified charges are *retained*, and the
only new entry accepted is a medium-only residual. -/
structure IncrementalLedger where
  /-- The charges already certified; they are retained verbatim. -/
  existing : List ℚ
  /-- The single new entry. -/
  residual : ℚ
  /-- Its source type. -/
  residualSource : ChargeSource
  /-- Type-safety field: only a medium-only residual may be inserted. -/
  residualIsMedium : residualSource = ChargeSource.medium
  /-- The ledger total. -/
  total : ℚ
  /-- The incremental accounting rule. -/
  total_eq : total = existing.sum + residual

/-- A **full-replacement** ledger: a full all-complement estimate replaces a listed set of
previously certified charges, which must be removed explicitly. -/
structure FullReplacementLedger where
  /-- The charges already certified. -/
  existing : List ℚ
  /-- The charges that the replacement supersedes; they must be removed. -/
  removed : List ℚ
  /-- Removal is only legal for charges that are actually on the books. -/
  removedMem : ∀ x ∈ removed, x ∈ existing
  /-- The replacing estimate. -/
  replacement : ℚ
  /-- Its source type. -/
  replacementSource : ChargeSource
  /-- Type-safety field: the replacement is a full all-complement estimate. -/
  replacementIsFull : replacementSource = ChargeSource.full
  /-- The ledger total. -/
  total : ℚ
  /-- The replacement accounting rule: the removed charges leave the books. -/
  total_eq : total = existing.sum - removed.sum + replacement

/-- **`incrementalLedger_retains`.**  `KERNEL-PROVED`.  An incremental ledger retains all
existing charges: removing the new residual returns exactly the old subtotal. -/
theorem incrementalLedger_retains (L : IncrementalLedger) :
    L.total - L.residual = L.existing.sum := by
  rw [L.total_eq]; ring

/-- **`incrementalLedger_rejects_full`.**  `KERNEL-PROVED`.  No incremental ledger carries a
full all-complement source in its residual slot. -/
theorem incrementalLedger_rejects_full (L : IncrementalLedger) :
    L.residualSource ≠ ChargeSource.full := by
  rw [L.residualIsMedium]; simp

/-- **`no_naive_full_insertion`.**  `KERNEL-PROVED`.  There is no coercion from a
full-replacement estimate into an incremental ledger keeping the same books: if the
replacement genuinely supersedes charges (`removed.sum ≠ 0`), then no `IncrementalLedger`
has the same existing charges, the same new entry and the same total. -/
theorem no_naive_full_insertion (F : FullReplacementLedger) (hrem : F.removed.sum ≠ 0) :
    ¬ ∃ L : IncrementalLedger,
        L.existing = F.existing ∧ L.residual = F.replacement ∧ L.total = F.total := by
  rintro ⟨L, hex, hres, htot⟩
  have h1 : L.total = F.existing.sum + F.replacement := by rw [L.total_eq, hex, hres]
  have h2 : F.total = F.existing.sum - F.removed.sum + F.replacement := F.total_eq
  rw [htot, h2] at h1
  exact hrem (by linarith)

/-- **`fullReplacement_requires_removal`.**  `KERNEL-PROVED`.  Conversely, the two totals
agree exactly when nothing had to be removed. -/
theorem fullReplacement_requires_removal (F : FullReplacementLedger) :
    F.total = F.existing.sum + F.replacement ↔ F.removed.sum = 0 := by
  rw [F.total_eq]
  constructor <;> intro h <;> linarith

end Effectivity
end Erdos287
