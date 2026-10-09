import RequestProject.Erdos287.PostQSigma.HardCore

/-!
# Erdős #287 — post-`Q_Σ` bank, §38: the conservative entropy estimate for `P = |Ω|`

**Status: BANK (proved in Lean).**

* `indepCount L` — the number of independent subsets of `{0, …, L-1}`;
* `indepCount_succ_succ_le` — `f(L+2) ≤ f(L+1) + f(L)` (path recursion);
* `indepCount_le` — `f(L) ≤ 2 β^L` with `β = 16181/10000 > φ`;
* `Ptot_eq_indepCount` — `P = |Ω(a,M)| = f(M - a - 1)` (shift invariance);
* `exp_ge_beta` — `β ≤ exp(967/2000)` (from the quadratic exponential bound, no transcendental
  axiom);
* `Ptot_lt_exp` — **entropy estimate**: `16M < 121a`, `a < M`, `M ≥ 3000` ⇒
  `P < exp(21M/50)`, i.e. `log P < (21/50) M`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

open Classical in
/-- Number of independent subsets of `{0, …, L-1}`. -/
noncomputable def indepCount (L : ℕ) : ℕ := ((Finset.range L).powerset.filter Indep).card

open Classical in
theorem indepCount_succ_succ_le (L : ℕ) :
    indepCount (L + 2) ≤ indepCount (L + 1) + indepCount L := by
  unfold indepCount
  set S := (Finset.range (L + 2)).powerset.filter Indep
  have hsplit : S = S.filter (fun E => L + 1 ∈ E) ∪ S.filter (fun E => ¬ (L + 1 ∈ E)) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  rw [hsplit]
  refine (Finset.card_union_le _ _).trans ?_
  rw [add_comm]
  refine add_le_add ?_ ?_
  · apply Finset.card_le_card
    intro E hE
    simp only [S, Finset.mem_filter, Finset.mem_powerset] at hE ⊢
    refine ⟨fun x hx => ?_, hE.1.2⟩
    have := Finset.mem_range.1 (hE.1.1 hx)
    have hx' : x ≠ L + 1 := fun h => hE.2 (h ▸ hx)
    exact Finset.mem_range.2 (by omega)
  · refine Finset.card_le_card_of_injOn (fun E => E.erase (L + 1)) ?_ ?_
    · intro E hE
      simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq]
        at hE ⊢
      refine ⟨fun x hx => ?_, fun x hx hx1 => hE.1.2 x (Finset.mem_of_mem_erase hx)
        (Finset.mem_of_mem_erase hx1)⟩
      have hxE := Finset.mem_of_mem_erase hx
      have hx1 := Finset.ne_of_mem_erase hx
      have := Finset.mem_range.1 (hE.1.1 hxE)
      have hxL : x ≠ L := fun h => hE.1.2 x hxE (h ▸ hE.2)
      exact Finset.mem_range.2 (by omega)
    · intro E hE F hF h
      simp only [S, Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hE hF
      have := congrArg (insert (L + 1)) h
      simp only [Finset.insert_erase hE.2, Finset.insert_erase hF.2] at this
      exact this

/-- `β = 16181/10000`, slightly above the golden ratio. -/
def beta : ℚ := 16181 / 10000

theorem indepCount_le (L : ℕ) : (indepCount L : ℚ) ≤ 2 * beta ^ L := by
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases L with _ | _ | L
    · classical
      have : indepCount 0 ≤ 1 := by
        unfold indepCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      have : (indepCount 0 : ℚ) ≤ 1 := by exact_mod_cast this
      simp only [pow_zero, mul_one]; linarith
    · classical
      have : indepCount 1 ≤ 2 := by
        unfold indepCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      have : (indepCount 1 : ℚ) ≤ 2 := by exact_mod_cast this
      norm_num [beta]; linarith
    · have h := indepCount_succ_succ_le L
      have h1 := ih (L + 1) (by omega)
      have h0 := ih L (by omega)
      have hb : (0 : ℚ) ≤ beta ^ L := by unfold beta; positivity
      have hβ : beta ^ (L + 2) ≥ beta ^ (L + 1) + beta ^ L := by
        have : beta ^ 2 ≥ beta + 1 := by norm_num [beta]
        calc beta ^ (L + 2) = beta ^ L * beta ^ 2 := by ring
          _ ≥ beta ^ L * (beta + 1) := mul_le_mul_of_nonneg_left this hb
          _ = beta ^ (L + 1) + beta ^ L := by ring
      calc (indepCount (L + 2) : ℚ) ≤ indepCount (L + 1) + indepCount L := by exact_mod_cast h
        _ ≤ 2 * beta ^ (L + 1) + 2 * beta ^ L := add_le_add h1 h0
        _ ≤ 2 * beta ^ (L + 2) := by linarith

/-- Shifting by `a + 1` identifies `Ω(a, M)` with the independent subsets of
`{0, …, M - a - 2}`. -/
theorem Ptot_eq_indepCount {a M : ℕ} : Ptot a M = indepCount (M - a - 1) := by
  classical
  unfold Ptot Omega indepCount
  have hI : Finset.Ioo a M = (Finset.range (M - a - 1)).map (addRightEmbedding (a + 1)) := by
    ext n
    simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - (a + 1), by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  set f := addRightEmbedding (a + 1)
  have hind : ∀ E : Finset ℕ, Indep (E.map f) ↔ Indep E := by
    intro E
    simp only [Indep, Finset.mem_map, f, addRightEmbedding_apply]
    constructor
    · intro h x hx hx1
      exact h (x + (a + 1)) ⟨x, hx, rfl⟩ ⟨x + 1, hx1, by ring⟩
    · rintro h _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have : y = x + 1 := by omega
      exact h x hx (this ▸ hy)
  have hset : ((Finset.range (M - a - 1)).map f).powerset.filter Indep =
      ((Finset.range (M - a - 1)).powerset.filter Indep).map
        ⟨Finset.map f, Finset.map_injective f⟩ := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hE, hi⟩
      obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hE
      exact ⟨u, ⟨hu, (hind u).1 hi⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hi⟩, rfl⟩
      exact ⟨Finset.map_subset_map.2 hu, (hind u).2 hi⟩
  rw [hI, hset, Finset.card_map]

/-- `β ≤ exp(967/2000)`, certified from `1 + x + x²/2 ≤ exp x` at `x = 967/8000`. -/
theorem exp_ge_beta : ((beta : ℚ) : ℝ) ≤ Real.exp (967 / 2000) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 967 / 8000) (by norm_num)
  have h4 : Real.exp (967 / 2000) = Real.exp (967 / 8000) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have hpos : (0 : ℝ) ≤ 1 + 967 / 8000 + (967 / 8000) ^ 2 / 2 := by norm_num
  calc ((beta : ℚ) : ℝ) ≤ (1 + 967 / 8000 + (967 / 8000) ^ 2 / 2) ^ 4 := by
        norm_num [beta]
    _ ≤ Real.exp (967 / 8000) ^ 4 := pow_le_pow_left₀ hpos h 4

/-- **Entropy estimate**: `log P < (21/50) M` in exponential form. -/
theorem Ptot_lt_exp {a M : ℕ} (haM : a < M) (h16 : 16 * M < 121 * a) (hM : 3000 ≤ M) :
    (Ptot a M : ℝ) < Real.exp (21 * M / 50) := by
  rw [Ptot_eq_indepCount]
  set L := M - a - 1 with hL
  have h1 : ((indepCount L : ℕ) : ℝ) ≤ 2 * ((beta : ℚ) : ℝ) ^ L := by
    have := indepCount_le L
    exact_mod_cast this
  have hb0 : (0 : ℝ) ≤ ((beta : ℚ) : ℝ) := by norm_num [beta]
  have h2 : (2 : ℝ) ≤ ((beta : ℚ) : ℝ) ^ 2 := by norm_num [beta]
  have h3 : 2 * ((beta : ℚ) : ℝ) ^ L ≤ ((beta : ℚ) : ℝ) ^ (L + 2) := by
    rw [pow_add]; nlinarith [pow_nonneg hb0 L]
  have h4 : ((beta : ℚ) : ℝ) ^ (L + 2) ≤ Real.exp (967 / 2000) ^ (L + 2) :=
    pow_le_pow_left₀ hb0 exp_ge_beta _
  rw [← Real.exp_nat_mul] at h4
  have hK : (121 : ℝ) * ((L + 2 : ℕ) : ℝ) < 105 * M + 121 * 2 := by
    have : 121 * (L + 2) < 105 * M + 242 := by omega
    exact_mod_cast this
  have hM' : (3000 : ℝ) ≤ M := by exact_mod_cast hM
  have h5 : ((L + 2 : ℕ) : ℝ) * (967 / 2000) < 21 * M / 50 := by linarith
  calc ((indepCount L : ℕ) : ℝ) ≤ 2 * ((beta : ℚ) : ℝ) ^ L := h1
    _ ≤ ((beta : ℚ) : ℝ) ^ (L + 2) := h3
    _ ≤ Real.exp (((L + 2 : ℕ) : ℝ) * (967 / 2000)) := h4
    _ < Real.exp (21 * M / 50) := Real.exp_lt_exp.2 h5

end Erdos287.PostQSigma
