import Mathlib

/-!
# Erdős #287 — Research Bank V26 §4.5–4.6: the dyadic source map

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**LEAN BANK.**
* `dyadic_mem` / `dyadic_unique` — every `n ≥ 1` lies in exactly one dyadic interval
  `[2^k, 2^{k+1})`, namely `k = ⌊log₂ n⌋`;
* `dyadic_partition_of_unity` — `Σ_{k<K} 1_{[2^k,2^{k+1})}(n) = 1` for `1 ≤ n < 2^K`;
* `dyadicBox` / `source_sum_by_boxes` — for any finite set of variable tuples and any source
  coefficient `F`, `Σ_m F(m) = Σ_{boxes b} Σ_{m ∈ box b} F(m)`: every source term is counted in
  exactly one dyadic box (source-level, not a length census).

Dyadicization alone does NOT remove the product constraint `x < m₁⋯m_k ≤ 2x`; that is the job of
the multiplicative boxes (`ProductIntervalBoxes.lean`).
-/

namespace Erdos287
namespace ResearchBankV26
namespace DyadicSourceMap

open Finset

theorem dyadic_mem {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1) :=
  ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) n⟩

theorem dyadic_unique {n k : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : k = Nat.log 2 n := by
  have hn : n ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
  exact ((Nat.log_eq_iff (Or.inr ⟨by norm_num, hn⟩)).2 ⟨h1, h2⟩).symm

/-- **Dyadic partition of unity** (LEAN BANK). -/
theorem dyadic_partition_of_unity {n K : ℕ} (hn : 1 ≤ n) (hK : n < 2 ^ K) :
    ∑ k ∈ Finset.range K, (if 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single (Nat.log 2 n)]
  · rw [if_pos (dyadic_mem hn)]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hk (dyadic_unique h1 h2)
  · intro h
    exfalso; apply h
    rw [Finset.mem_range]
    have := (dyadic_mem hn).1
    by_contra hge
    push_neg at hge
    have : 2 ^ K ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) hge
    omega

/-- The dyadic box of a variable tuple. -/
def dyadicBox {k : ℕ} (m : Fin k → ℕ) : Fin k → ℕ := fun i => Nat.log 2 (m i)

/-- **Source sum by boxes** (LEAN BANK): each source term lies in exactly one dyadic box. -/
theorem source_sum_by_boxes {k : ℕ} (S : Finset (Fin k → ℕ)) (F : (Fin k → ℕ) → ℝ) :
    ∑ m ∈ S, F m = ∑ b ∈ S.image dyadicBox, ∑ m ∈ S.filter (fun m => dyadicBox m = b), F m :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hm => Finset.mem_image_of_mem _ hm) F).symm

end DyadicSourceMap
end ResearchBankV26
end Erdos287
