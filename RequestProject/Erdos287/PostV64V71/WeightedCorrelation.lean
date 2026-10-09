import RequestProject.Erdos287.PostV64V71.ExceptionAccounting

/-!
# Erdős #287 — V71 exact weighted adjacent correlation `C_K(M) ≤ D_Λ(M)`

**Status: BANK (LEAN PROVED).**  Finite combinatorics only.

* `Iset M = {n : M/2 < n < 3M/4}` (as `M < 2n`, `4n < 3M`);
* `fK K n = ∑_{k ≤ K, k ∣ n} Λ(n/k)`;
* `CK M K = ∑_{n, m ∈ I, |n - m| = 1} f_K(n) f_K(m)` (the authoritative combinatorial
  definition);
* `CK_eq_sum_quad` — the expansion of `C_K` as a sum over quadruples `(n, m, k, t)`;
* `weighted_subbox_le_full_supply` — for `4K ≤ H`: `C_K(M) ≤ D_Λ(M)` via the exact subbox
  dictionary `(n, m, k, t) ↦ (k, n/k, t, m/t, n - m)`; in particular for `K = ⌊H/4⌋`.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- The interval `I = (M/2, 3M/4)`. -/
def Iset (M : ℕ) : Finset ℕ := (Finset.range (M + 1)).filter (fun n => M < 2 * n ∧ 4 * n < 3 * M)

theorem mem_Iset {M n : ℕ} : n ∈ Iset M ↔ M < 2 * n ∧ 4 * n < 3 * M := by
  simp only [Iset, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

/-- `f_K(n) = ∑_{k ≤ K, k ∣ n} Λ(n/k)`. -/
noncomputable def fK (K n : ℕ) : ℝ := ∑ k ∈ (Finset.Icc 1 K).filter (· ∣ n), LambdaW (n / k)

/-- Adjacency `|n - m| = 1`. -/
def Adj (n m : ℕ) : Prop := n = m + 1 ∨ m = n + 1

instance (n m : ℕ) : Decidable (Adj n m) := by unfold Adj; infer_instance

/-- **`C_K(M)`**: the exact adjacent weighted correlation. -/
noncomputable def CK (M K : ℕ) : ℝ :=
  ∑ n ∈ Iset M, ∑ m ∈ Iset M, if Adj n m then fK K n * fK K m else 0

/-- The quadruple index set `{(n, m, k, t) : n, m ∈ I adjacent, k, t ≤ K, k ∣ n, t ∣ m}`. -/
def quadSet (M K : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Iset M ×ˢ Iset M) ×ˢ (Finset.Icc 1 K ×ˢ Finset.Icc 1 K)).filter
    (fun x => Adj x.1.1 x.1.2 ∧ x.2.1 ∣ x.1.1 ∧ x.2.2 ∣ x.1.2)

/-- Expansion of `C_K` over quadruples. -/
theorem CK_eq_sum_quad (M K : ℕ) :
    CK M K = ∑ x ∈ quadSet M K, LambdaW (x.1.1 / x.2.1) * LambdaW (x.1.2 / x.2.2) := by
  unfold CK quadSet
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_product]
  unfold fK
  rw [Finset.sum_mul_sum, Finset.sum_filter]
  by_cases hadj : Adj n m
  · rw [if_pos hadj]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_filter]
    by_cases hk : k ∣ n
    · rw [if_pos hk]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : t ∣ m
      · rw [if_pos ht, if_pos ⟨hadj, hk, ht⟩]
      · rw [if_neg ht, if_neg (fun h => ht h.2.2)]
    · rw [if_neg hk]
      exact (Finset.sum_eq_zero fun t _ => if_neg (fun h => hk h.2.1)).symm
  · rw [if_neg hadj]
    symm
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun t _ => if_neg (fun h => hadj h.1)

/-- The subbox dictionary `(n, m, k, t) ↦ (k, n/k, t, m/t, n - m)`. -/
def quadToTup (x : (ℕ × ℕ) × (ℕ × ℕ)) : DTup :=
  (x.2.1, x.1.1 / x.2.1, x.2.2, x.1.2 / x.2.2, (x.1.1 : ℤ) - x.1.2)

theorem quadToTup_mem {M K H : ℕ} (hKH : 4 * K ≤ H) {x : (ℕ × ℕ) × (ℕ × ℕ)}
    (hx : x ∈ quadSet M K) : quadToTup x ∈ detBox M H := by
  obtain ⟨⟨n, m⟩, ⟨k, t⟩⟩ := x
  simp only [quadSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨⟨hn, hm⟩, ⟨hk1, hkK⟩, ⟨ht1, htK⟩⟩, hadj, hkn, htm⟩ := hx
  rw [mem_Iset] at hn hm
  have hnk : k * (n / k) = n := Nat.mul_div_cancel' hkn
  have hmt : t * (m / t) = m := Nat.mul_div_cancel' htm
  have hHpos : 0 < H := by omega
  -- `n/k > M/H` since `(n/k) H ≥ (n/k) 4k = 4n > M`
  have hq : M / H < n / k := by
    rw [Nat.div_lt_iff_lt_mul hHpos]
    have : (n / k) * (4 * k) ≤ (n / k) * H := Nat.mul_le_mul_left _ (by omega)
    have h4 : (n / k) * (4 * k) = 4 * n := by
      calc (n / k) * (4 * k) = 4 * (k * (n / k)) := by ring
        _ = 4 * n := by rw [hnk]
    omega
  have hr : M / H < m / t := by
    rw [Nat.div_lt_iff_lt_mul hHpos]
    have : (m / t) * (4 * t) ≤ (m / t) * H := Nat.mul_le_mul_left _ (by omega)
    have h4 : (m / t) * (4 * t) = 4 * m := by
      calc (m / t) * (4 * t) = 4 * (t * (m / t)) := by ring
        _ = 4 * m := by rw [hmt]
    omega
  rw [mem_detBox]
  simp only [quadToTup, DTup.k, DTup.q, DTup.t, DTup.r, DTup.eps]
  refine ⟨⟨hk1, by omega⟩, ⟨hq, le_trans (Nat.div_le_self _ _) (by omega)⟩, ⟨ht1, by omega⟩,
    ⟨hr, le_trans (Nat.div_le_self _ _) (by omega)⟩, ?_, ?_, ?_, ?_⟩
  · rcases hadj with h | h
    · left; omega
    · right; omega
  · rw [hnk, hmt]
  · rw [hnk]; exact hn.1
  · rw [hnk]; exact hn.2

theorem quadToTup_injOn (M K : ℕ) : Set.InjOn quadToTup (quadSet M K) := by
  intro x hx x' hx' h
  obtain ⟨⟨n, m⟩, ⟨k, t⟩⟩ := x
  obtain ⟨⟨n', m'⟩, ⟨k', t'⟩⟩ := x'
  simp only [quadSet, Finset.coe_filter, Set.mem_setOf_eq] at hx hx'
  simp only [quadToTup, Prod.mk.injEq] at h
  obtain ⟨hkk, hq, htt, hr, -⟩ := h
  subst hkk htt
  have hn : n = n' := by
    rw [← Nat.mul_div_cancel' hx.2.2.1, ← Nat.mul_div_cancel' hx'.2.2.1, hq]
  have hm : m = m' := by
    rw [← Nat.mul_div_cancel' hx.2.2.2, ← Nat.mul_div_cancel' hx'.2.2.2, hr]
  rw [hn, hm]

/-- **`C_K(M) ≤ D_Λ(M)`** whenever `4K ≤ H` (exact subbox dictionary). -/
theorem weighted_subbox_le_full_supply (M K H : ℕ) (hKH : 4 * K ≤ H) :
    CK M K ≤ DLambda M H := by
  rw [CK_eq_sum_quad]
  have himg : ∑ x ∈ quadSet M K, LambdaW (x.1.1 / x.2.1) * LambdaW (x.1.2 / x.2.2) =
      ∑ y ∈ (quadSet M K).image quadToTup, LambdaW y.q * LambdaW y.r := by
    rw [Finset.sum_image (quadToTup_injOn M K)]
    rfl
  rw [himg]
  unfold DLambda Dw
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ =>
    mul_nonneg (LambdaW_nonneg _) (LambdaW_nonneg _)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  exact quadToTup_mem hKH hx

/-- The V71 instance `K = ⌊H/4⌋`. -/
theorem weighted_subbox_le_full_supply_quarter (M H : ℕ) : CK M (H / 4) ≤ DLambda M H :=
  weighted_subbox_le_full_supply M (H / 4) H (by omega)

end Erdos287.PostV64V71
