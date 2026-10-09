import Mathlib
import RequestProject.Erdos287.AllQResummation

/-!
# Erdős #287 effectivity — the truncated divisor coefficient `A_z(m)` (§39)

```
TRUNCATED DIVISOR IDENTITY : KERNEL-PROVED
ALL-q DIVISOR IDENTITY     : REUSED (AllQResummation, §28)
NAIVE IDENTITY A_z = B(zm)/B(z) : REFUTED (firewall)
ERDŐS #287                 : OPEN
```

The current source carries the *truncated* divisor coefficient

    A_z(m) = ∑_{q ∣ m, q ∈ admissible} β(q),

where the admissible denominator set is a sub-collection of the coprime divisors.  The exact
relation to the complete all-`q` identity of §28

    ∑_{q ∣ m, (q,z) = 1} β(q) = B(z m) / B(z)

is **not** equality but equality *after subtraction* of the excluded closed-owner divisor
sums:

    A_z(m) = B(z m)/B(z) − ∑_{q ∣ m, (q,z)=1, q ∉ admissible} β(q)   (`truncated_divisor_identity`).

`truncated_ne_complete` refutes the naive identity `A_z(m) = B(zm)/B(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §39.1  The truncated coefficient -/

/-- `A_z(m) = ∑_{q ∣ m, q admissible} β(q)`, for a decidable admissible denominator set. -/
def AzTruncated (adm : ℕ → Prop) [DecidablePred adm] (m : ℕ) : ℚ :=
  ∑ q ∈ m.divisors with adm q, beta q

/-- The complete coprime divisor coefficient. -/
def AzComplete (z m : ℕ) : ℚ := ∑ q ∈ m.divisors with Nat.Coprime q z, beta q

/-- The excluded (already-owned) part. -/
def AzExcluded (z : ℕ) (adm : ℕ → Prop) [DecidablePred adm] (m : ℕ) : ℚ :=
  ∑ q ∈ m.divisors with (Nat.Coprime q z ∧ ¬ adm q), beta q

/-- **`truncated_divisor_decomposition`.**  `KERNEL-PROVED`.  If every admissible denominator
is coprime to `z`, the truncated coefficient is the complete one minus the excluded sums. -/
theorem truncated_divisor_decomposition {z : ℕ} (adm : ℕ → Prop) [DecidablePred adm]
    (hadm : ∀ q, adm q → Nat.Coprime q z) (m : ℕ) :
    AzTruncated adm m = AzComplete z m - AzExcluded z adm m := by
  unfold AzTruncated AzComplete AzExcluded
  rw [eq_sub_iff_add_eq, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : adm q
  · simp [hq, hadm q hq]
  · by_cases hc : Nat.Coprime q z <;> simp [hq, hc]

/-- **`truncated_divisor_identity`.**  `KERNEL-PROVED`.  The exact relation between the
truncated coefficient and the complete all-`q` identity of §28. -/
theorem truncated_divisor_identity (B1 : ℚ) (hB1 : B1 ≠ 0) {z m : ℕ} (hz : z ≠ 0) (hm : m ≠ 0)
    (adm : ℕ → Prop) [DecidablePred adm] (hadm : ∀ q, adm q → Nat.Coprime q z) :
    AzTruncated adm m = B B1 (z * m) / B B1 z - AzExcluded z adm m := by
  rw [truncated_divisor_decomposition adm hadm m, AzComplete,
    allQ_divisor_identity B1 hB1 hz hm]

/-- **`truncated_eq_complete_iff`.**  `KERNEL-PROVED`.  The truncated coefficient equals the
complete divisor coefficient exactly when nothing is excluded. -/
theorem truncated_eq_complete_iff {z : ℕ} (adm : ℕ → Prop) [DecidablePred adm]
    (hadm : ∀ q, adm q → Nat.Coprime q z) (m : ℕ) :
    AzTruncated adm m = AzComplete z m ↔ AzExcluded z adm m = 0 := by
  rw [truncated_divisor_decomposition adm hadm m]
  constructor <;> intro h <;> linarith

/-- **`truncated_ne_complete`.**  `KERNEL-PROVED`.  Firewall: one may **not** write
`A_z(m) = B(zm)/B(z)` without the subtraction.  With `z = 1`, `m = 3` and an empty admissible
set the truncated coefficient is `0` while the complete one is `1 + β(3) = 2`. -/
theorem truncated_ne_complete :
    AzTruncated (fun _ => False) 3 ≠ AzComplete 1 3 := by
  have hdiv : (3 : ℕ).divisors = ({1, 3} : Finset ℕ) := by decide
  have hbeta3 : beta 3 = 1 := by
    rw [beta_prime (by norm_num) (by norm_num)]; norm_num
  have h1 : AzTruncated (fun _ => False) 3 = 0 := by
    simp [AzTruncated]
  have h2 : AzComplete 1 3 = 2 := by
    unfold AzComplete
    rw [hdiv]
    rw [show (Finset.filter (fun q => Nat.Coprime q 1) ({1, 3} : Finset ℕ)) = {1, 3} from by
      decide]
    rw [show ({1, 3} : Finset ℕ) = insert 1 {3} from rfl, Finset.sum_insert (by decide),
      Finset.sum_singleton, hbeta3, beta_one]
    norm_num
  rw [h1, h2]
  norm_num

end Effectivity
end Erdos287
