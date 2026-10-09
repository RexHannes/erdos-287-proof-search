import RequestProject.Erdos287.SourceChain.Physical.Factorization.Mult

/-!
# Erdős #287 — Pascadi's Proposition 5.2 for finite vectors and for actual moduli

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `VecHyp D P r` — a finite vector `P₀ ≥ ⋯ ≥ P_{r-1} ≥ 1` in Pascadi's `𝒟⁺_r(D)` (Def. 5.1,
  `(5.2)`), only the odd (1-indexed) prefix conditions.
* `VecHyp.prod_le` — such a vector has `∏ P_i ≤ D` (needed for the padding).
* `prop52_vector` — Pascadi Prop. 5.2 for such vectors: the padding by `1` handles `r = 0`
  (`d = 1`) and `r < 6`.
* `InDplus D d` — **Pascadi Definition 5.1** for a positive integer, using the *actual ordered
  prime-factor list with multiplicity* `p₁ ≥ p₂ ≥ ⋯ ≥ p_r` (`descPrimes d`).
* `prop52_nat` — **Pascadi Proposition 5.2**: for every `d ∈ 𝒟⁺(x^{3/5-50δ})` there are
  `d = d₁ d₂ d₃` (products of the coloured primes) obeying (5.3).
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.Factor

/-- Pad a length-`r` vector by `1`. -/
noncomputable def padOne (P : ℕ → ℝ) (r : ℕ) : ℕ → ℝ := fun i => if i < r then P i else 1

/-- A finite vector in Pascadi's `𝒟⁺_r(D)`. -/
structure VecHyp (D : ℝ) (P : ℕ → ℝ) (r : ℕ) : Prop where
  one_le : ∀ i < r, 1 ≤ P i
  anti : ∀ i j, i ≤ j → j < r → P j ≤ P i
  plus : ∀ j < r, Even j → (∏ i ∈ range j, P i) * P j ^ 3 ≤ D

lemma VecHyp.prod_le {D : ℝ} {P : ℕ → ℝ} {r : ℕ} (h : VecHyp D P r) (hD : 1 ≤ D) :
    ∏ i ∈ range r, P i ≤ D := by
  have hpos : ∀ j ≤ r, 0 ≤ ∏ i ∈ range j, P i := fun j hj =>
    prod_nonneg (fun i hi => le_trans zero_le_one (h.one_le i (by simp at hi; omega)))
  rcases r with _ | m
  · simpa using hD
  rcases Nat.even_or_odd m with hm | hm
  · have h1 := h.plus m (by omega) hm
    have hPm := h.one_le m (by omega)
    rw [prod_range_succ]
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_left (le_self_pow₀ hPm (by norm_num)) (hpos m (by omega))
  · obtain ⟨k, rfl⟩ := hm
    have h1 := h.plus (2 * k) (by omega) (even_two_mul k)
    have hPk := h.one_le (2 * k) (by omega)
    have hPk1 := h.one_le (2 * k + 1) (by omega)
    have ha := h.anti (2 * k) (2 * k + 1) (by omega) (by omega)
    rw [prod_range_succ, prod_range_succ, mul_assoc]
    refine le_trans ?_ h1
    refine mul_le_mul_of_nonneg_left ?_ (hpos (2 * k) (by omega))
    calc P (2 * k) * P (2 * k + 1) ≤ P (2 * k) * P (2 * k) := by nlinarith
      _ ≤ P (2 * k) ^ 3 := by nlinarith

lemma prod_padOne_of_le (P : ℕ → ℝ) (r j : ℕ) (hj : j ≤ r) :
    ∏ i ∈ range j, padOne P r i = ∏ i ∈ range j, P i :=
  prod_congr rfl (fun i hi => by simp [padOne, show i < r by simp at hi; omega])

lemma prod_padOne_of_ge (P : ℕ → ℝ) (r j : ℕ) (hj : r ≤ j) :
    ∏ i ∈ range j, padOne P r i = ∏ i ∈ range r, P i := by
  rw [← prod_range_mul_prod_Ico _ hj, prod_padOne_of_le P r r le_rfl]
  have h1 : ∏ i ∈ Ico r j, padOne P r i = 1 :=
    prod_eq_one (fun i hi => by simp [padOne, show ¬ i < r by simp at hi; omega])
  rw [h1, mul_one]

lemma VecHyp.pad {D : ℝ} {P : ℕ → ℝ} {r : ℕ} (h : VecHyp D P r) (hD : 1 ≤ D) :
    (∀ i, 1 ≤ padOne P r i) ∧ Antitone (padOne P r) ∧
      ∀ j, Even j → (∏ i ∈ range j, padOne P r i) * padOne P r j ^ 3 ≤ D := by
  refine ⟨fun i => ?_, fun i j hij => ?_, fun j hj => ?_⟩
  · unfold padOne; split_ifs with hi
    · exact h.one_le i hi
    · exact le_rfl
  · unfold padOne
    by_cases hj : j < r
    · rw [if_pos hj, if_pos (by omega)]; exact h.anti i j hij hj
    · rw [if_neg hj]; split_ifs with hi
      · exact h.one_le i hi
      · exact le_rfl
  · by_cases hjr : j < r
    · rw [prod_padOne_of_le P r j hjr.le]
      simpa [padOne, hjr] using h.plus j hjr hj
    · rw [prod_padOne_of_ge P r j (by omega)]
      simpa [padOne, hjr] using h.prod_le hD

lemma cprod_padOne (P : ℕ → ℝ) (r : ℕ) (c : ℕ → Fin 3) (k : Fin 3) :
    cprod (padOne P r) c k r = cprod P c k r :=
  prod_congr rfl (fun i hi => by simp at hi; simp [padOne, hi.1])

/-- **Pascadi, Proposition 5.2** for a finite vector in `𝒟⁺_r(x^{3/5-50δ})`, with every
published parameter condition. -/
theorem prop52_vector {x δ N : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ' : δ < 1 / 100000)
    (hN1 : x ^ (2 * δ) ≤ N) (hN2 : N ≤ x ^ (1 / 3 + δ)) {P : ℕ → ℝ} {r : ℕ}
    (h : VecHyp (x ^ (3 / 5 - 50 * δ)) P r) :
    ∃ c : ℕ → Fin 3, Sys53 x δ N (cprod P c 0 r) (cprod P c 1 r) (cprod P c 2 r) := by
  have hD : 1 ≤ x ^ (3 / 5 - 50 * δ) := one_le_rpow hx.le (by linarith)
  obtain ⟨h1, h2, h3⟩ := h.pad hD
  obtain ⟨c, hc⟩ := prop52_real ⟨hx, hδ, hδ', hN1, hN2, h1, h2, h3⟩ r
  refine ⟨c, ?_⟩
  simpa only [cprod_padOne] using hc

/-! ### Actual moduli: the ordered prime-factor list -/

/-- The prime factors of `d` with multiplicity, in **decreasing** order `p₁ ≥ p₂ ≥ ⋯`. -/
def descPrimes (d : ℕ) : List ℕ := d.primeFactorsList.reverse

/-- The `i`-th prime factor (`0`-indexed, `1` beyond the end), as a real number. -/
noncomputable def primeAt (d i : ℕ) : ℝ := ((descPrimes d).getD i 1 : ℕ)

/-- **Pascadi, Definition 5.1**: `d ∈ 𝒟⁺(D)` iff `p₁ ⋯ p_{j-1} p_j³ ≤ D` for every odd `j ≤ r`
(`0`-indexed: even `j`), with the actual decreasing prime list. -/
def InDplus (D : ℝ) (d : ℕ) : Prop :=
  ∀ j < (descPrimes d).length, Even j → (∏ i ∈ range j, primeAt d i) * primeAt d j ^ 3 ≤ D

/-- The colour-`k` factor of `d`: the product of the primes of colour `k`. -/
noncomputable def natFactor (d : ℕ) (c : ℕ → Fin 3) (k : Fin 3) : ℕ :=
  ∏ i ∈ (range (descPrimes d).length).filter (fun i => c i = k), (descPrimes d).getD i 1

lemma prod_getD_range (l : List ℕ) : ∏ i ∈ range l.length, l.getD i 1 = l.prod := by
  rw [prod_range (fun i => l.getD i 1), ← Fin.prod_univ_getElem]
  exact prod_congr rfl (fun i _ => List.getD_eq_getElem l 1 i.2)

lemma natFactor_mul (d : ℕ) (hd : d ≠ 0) (c : ℕ → Fin 3) :
    natFactor d c 0 * natFactor d c 1 * natFactor d c 2 = d := by
  unfold natFactor
  have := Finset.prod_fiberwise (range (descPrimes d).length) c (fun i => (descPrimes d).getD i 1)
  rw [Fin.prod_univ_three] at this
  rw [this, prod_getD_range, descPrimes, List.prod_reverse, Nat.prod_primeFactorsList hd]

lemma descPrimes_vecHyp (D : ℝ) (d : ℕ) (hD : InDplus D d) :
    VecHyp D (primeAt d) (descPrimes d).length := by
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_, hD⟩
  · unfold primeAt
    rw [List.getD_eq_getElem _ _ hi]
    have hp : Nat.Prime (descPrimes d)[i] :=
      Nat.prime_of_mem_primeFactorsList (List.mem_reverse.1 (List.getElem_mem hi))
    exact_mod_cast hp.one_lt.le
  · unfold primeAt
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by omega)]
    have hs : (descPrimes d).SortedGE := List.sortedGE_reverse.2 (Nat.primeFactorsList_sorted d)
    have := hs (show (⟨i, by omega⟩ : Fin (descPrimes d).length) ≤ ⟨j, hj⟩ from hij)
    exact_mod_cast this

/-- **Pascadi, Proposition 5.2** for actual moduli: every `d ∈ 𝒟⁺(x^{3/5-50δ})` factors as
`d = d₁ d₂ d₃` (a colouring of its ordered prime factors) with
`d₁ ≤ N x^{-δ}`, `N² d₂ d₃² ≤ x^{1-δ}`, `N² d₂⁵ d₃² ≤ x^{2-δ}`. -/
theorem prop52_nat {x δ N : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ' : δ < 1 / 100000)
    (hN1 : x ^ (2 * δ) ≤ N) (hN2 : N ≤ x ^ (1 / 3 + δ)) {d : ℕ} (hd : d ≠ 0)
    (hD : InDplus (x ^ (3 / 5 - 50 * δ)) d) :
    ∃ c : ℕ → Fin 3, natFactor d c 0 * natFactor d c 1 * natFactor d c 2 = d ∧
      Sys53 x δ N (natFactor d c 0) (natFactor d c 1) (natFactor d c 2) := by
  obtain ⟨c, hc⟩ := prop52_vector hx hδ hδ' hN1 hN2 (descPrimes_vecHyp _ d hD)
  refine ⟨c, natFactor_mul d hd c, ?_⟩
  have e : ∀ k, (natFactor d c k : ℝ) = cprod (primeAt d) c k (descPrimes d).length := by
    intro k; unfold natFactor cprod primeAt; push_cast; rfl
  simpa only [e] using hc

end Erdos287.Physical.Factor
