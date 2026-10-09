import RequestProject.Erdos287.PostQSigma.Conductor
import RequestProject.Erdos287.PostQSigma.PathCount

/-!
# Erdős #287 — post-`Q_Σ` bank, §31 (V64): physical resonance, prime case

**Status: BANK (exact parts proved in Lean).**  Purpose: firewall showing that a prime-conductor
"square-root" Module A (`|A_p(T)| ≤ p^{1/2+o(1)} P`) cannot be universal on physical sources.

* `prime_block_identity` — for a prime `p ∣ W`: `A_p(T) = p · N_p(T) - P` (abstract), and
  `physical_prime_block_identity` (physical source);
* `prime_resonance_dvd_iff` — for `0 < a < p < M < 2p` (in particular the V64 family
  `M = 2p - 1`, `a = ⌊M/4⌋`, `p ≥ 3`, see `v64_family_hyp`): for every `E ∈ Ω`,
  `p ∣ X(E) ↔ p ∈ E`;
* `physical_prime_resonance` — hence `A_p(T) = p · #{E ∈ Ω : p ∈ E} - P` on that family.

The Fibonacci evaluation `P = f(M-a-1)` is `Ptot_eq_indepCount` (path count);
`#{E ∈ Ω : p ∈ E} = f(p-a-2) · f(M-p-2)` is `forced_count_fib` (proved), giving
`prime_resonance_fib`: `A_p(T) = p · f(p-a-2) f(M-p-2) - f(M-a-1)`.  The asymptotic ratio
`f(p-a-2) f(M-p-2) / f(M-a-1) → const > 0` (Binet) is **not** formalised here (paper-level /
elementary external lemma); with it, `A_p(T) ≍ p·P`, contradicting any universal
`p^{1/2+o(1)} P` bound.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- **Prime block identity** `A_p = p N_p - P` (abstract form). -/
theorem prime_block_identity {α : Type*} (Ω : Finset α) (Bf : α → ℤ) (T : ℤ) (W : ℕ)
    (hW : 0 < W) {p : ℕ} (hp : p.Prime) (hpW : p ∣ W) :
    Acond Ω Bf T W p =
      (p : ℂ) * ((Ω.filter (fun E => (p : ℤ) ∣ Bf E - T)).card : ℂ) - Ω.card := by
  have h := divisor_block_identity Ω Bf T W hpW hW
  rw [hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne'), A_one Ω Bf T W hW] at h
  rw [← h]; ring

/-- Physical prime block identity. -/
theorem physical_prime_block_identity {a M : ℕ} (ha : 0 < a) {p : ℕ} (hp : p.Prime)
    (hpW : p ∣ W a M ∅) :
    Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) p =
      (p : ℂ) * (((Omega a M).filter (fun E => (p : ℤ) ∣ Xd a M E)).card : ℂ) - Ptot a M := by
  have hW := Nat.pos_of_ne_zero (W_ne_zero (M := M) (R := ∅) ha)
  rw [prime_block_identity _ _ _ _ hW hp hpW]
  rfl

/-- A prime dividing no element does not divide the lcm. -/
lemma prime_not_dvd_lcm {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (h : ∀ n ∈ s, ¬ p ∣ n) :
    ¬ p ∣ s.lcm id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.ne_one]
  | insert n s hn ih =>
    rw [Finset.lcm_insert]
    intro hd
    have := hd.trans (Nat.lcm_dvd_mul n (s.lcm id))
    rcases (Nat.Prime.dvd_mul hp).1 this with h1 | h1
    · exact h n (Finset.mem_insert_self _ _) h1
    · exact ih (fun m hm => h m (Finset.mem_insert_of_mem hm)) h1

section Resonance

variable {a M p : ℕ} (hp : p.Prime) (ha : 0 < a) (hap : a < p) (hpM : p < M) (hM : M < 2 * p)
include hp ha hap hpM hM

omit hp ha hM in
lemma p_mem_B : p ∈ B a M ∅ := mem_B.2 ⟨hap.le, hpM.le, by simp⟩

omit hp hap hpM in
lemma not_dvd_of_ne {n : ℕ} (hn : n ∈ B a M ∅) (hne : n ≠ p) : ¬ p ∣ n := by
  rintro ⟨c, rfl⟩
  obtain ⟨h1, h2, -⟩ := mem_B.1 hn
  rcases c with _ | _ | c
  · omega
  · exact hne (by ring)
  · nlinarith

lemma p_dvd_W_div {n : ℕ} (hn : n ∈ B a M ∅) (hne : n ≠ p) : p ∣ W a M ∅ / n := by
  have hpW : p ∣ W a M ∅ := dvd_W_of_mem_B (p_mem_B hap hpM)
  rw [← Nat.mul_div_cancel' (dvd_W_of_mem_B hn)] at hpW
  rcases (Nat.Prime.dvd_mul hp).1 hpW with h | h
  · exact absurd h (not_dvd_of_ne ha hM hn hne)
  · exact h

lemma not_p_dvd_W_div_p : ¬ p ∣ W a M ∅ / p := by
  classical
  set L0 := ((B a M ∅).erase p).lcm id
  have hL0 : ¬ p ∣ L0 := prime_not_dvd_lcm hp _ (fun n hn =>
    not_dvd_of_ne ha hM (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn))
  have hWd : W a M ∅ ∣ p * L0 := by
    apply Finset.lcm_dvd
    intro n hn
    by_cases h : n = p
    · subst h; exact Dvd.intro _ rfl
    · exact (Finset.dvd_lcm (s := (B a M ∅).erase p) (f := id)
        (Finset.mem_erase.2 ⟨h, hn⟩)).trans (Dvd.intro_left _ rfl)
  intro hd
  have hpW : p ∣ W a M ∅ := dvd_W_of_mem_B (p_mem_B hap hpM)
  have : p * p ∣ p * L0 := by
    refine (?_ : p * p ∣ W a M ∅).trans hWd
    rw [← Nat.mul_div_cancel' hpW]
    exact Nat.mul_dvd_mul_left p hd
  exact hL0 (Nat.dvd_of_mul_dvd_mul_left hp.pos this)

/-- Mod-`p` reduction of a weighted sum over a subset of `B`. -/
lemma sum_mod_p (s : Finset ℕ) (hs : s ⊆ B a M ∅) :
    ∃ u : ℤ, ∑ n ∈ s, ((W a M ∅ / n : ℕ) : ℤ) =
      (if p ∈ s then ((W a M ∅ / p : ℕ) : ℤ) else 0) + p * u := by
  classical
  have hd : (p : ℤ) ∣ ∑ n ∈ s.filter (fun n => n ≠ p), ((W a M ∅ / n : ℕ) : ℤ) := by
    apply Finset.dvd_sum
    intro n hn
    obtain ⟨hns, hne⟩ := Finset.mem_filter.1 hn
    exact Int.natCast_dvd_natCast.2 (p_dvd_W_div hp ha hap hpM hM (hs hns) hne)
  obtain ⟨u, hu⟩ := hd
  refine ⟨u, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n = p), hu]
  congr 1
  rw [Finset.filter_eq']
  split_ifs <;> simp

/-- **Prime resonance reduction**: `p ∣ X(E) ↔ p ∈ E` for every `E ∈ Ω`. -/
theorem prime_resonance_dvd_iff {E : Finset ℕ} (hE : E ∈ Omega a M) :
    (p : ℤ) ∣ Xd a M E ↔ p ∈ E := by
  have hEB : E ⊆ B a M ∅ := fun n hn => by
    have := Finset.mem_Ioo.1 ((mem_Omega.1 hE).1 hn)
    exact mem_B.2 ⟨by omega, by omega, by simp⟩
  obtain ⟨u, hu⟩ := sum_mod_p hp ha hap hpM hM E hEB
  obtain ⟨v, hv⟩ := sum_mod_p hp ha hap hpM hM (B a M ∅) (Finset.Subset.refl _)
  have hpW : p ∣ W a M ∅ := dvd_W_of_mem_B (p_mem_B hap hpM)
  obtain ⟨w, hw⟩ := hpW
  have hX : Xd a M E = (if p ∈ E then ((W a M ∅ / p : ℕ) : ℤ) else 0)
      - ((W a M ∅ / p : ℕ) : ℤ) + p * (u - v + w) := by
    rw [Xd, cast_Bm, hu, T, hv, if_pos (p_mem_B hap hpM), hw]
    push_cast; ring
  have hc : ¬ (p : ℤ) ∣ ((W a M ∅ / p : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]; exact not_p_dvd_W_div_p hp ha hap hpM hM
  rw [hX, dvd_add_left (dvd_mul_right _ _)]
  split_ifs with h
  · simp [h]
  · simp only [zero_sub, dvd_neg, h, iff_false]
    exact hc

/-- **Physical prime resonance**: `A_p(T) = p · #{E ∈ Ω : p ∈ E} - P`. -/
theorem physical_prime_resonance :
    Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) p =
      (p : ℂ) * (((Omega a M).filter (fun E => p ∈ E)).card : ℂ) - Ptot a M := by
  classical
  rw [physical_prime_block_identity ha hp (dvd_W_of_mem_B (p_mem_B hap hpM))]
  rw [Finset.filter_congr (fun E hE => prime_resonance_dvd_iff hp ha hap hpM hM hE)]

end Resonance

/-- The V64 family `M = 2p - 1`, `a = ⌊M/4⌋` satisfies the hypotheses for `p ≥ 3`. -/
theorem v64_family_hyp {p : ℕ} (hp3 : 3 ≤ p) :
    0 < (2 * p - 1) / 4 ∧ (2 * p - 1) / 4 < p ∧ p < 2 * p - 1 ∧ 2 * p - 1 < 2 * p := by
  refine ⟨Nat.div_pos (by omega) (by norm_num), ?_, by omega, by omega⟩
  omega

/-- The V64 family instance of `prime_resonance_dvd_iff`. -/
theorem v64_prime_resonance {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {E : Finset ℕ}
    (hE : E ∈ Omega ((2 * p - 1) / 4) (2 * p - 1)) :
    (p : ℤ) ∣ Xd ((2 * p - 1) / 4) (2 * p - 1) E ↔ p ∈ E := by
  obtain ⟨h1, h2, h3, h4⟩ := v64_family_hyp hp3
  exact prime_resonance_dvd_iff hp h1 h2 h3 h4 hE

end Erdos287.PostQSigma

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- **Forced-vertex product formula**: independent subsets of `(a, M)` containing `p`
(`a < p < M`) split as an independent subset of `(a, p-1)` times one of `(p+1, M)`. -/
theorem forced_count_eq {a M p : ℕ} (hap : a < p) (hpM : p < M) :
    ((Omega a M).filter (fun E => p ∈ E)).card = Ptot a (p - 1) * Ptot (p + 1) M := by
  classical
  rw [Ptot, Ptot, ← Finset.card_product]
  symm
  refine Finset.card_nbij' (fun LR => insert p (LR.1 ∪ LR.2))
    (fun E => (E.filter (· < p), E.filter (p < ·))) ?_ ?_ ?_ ?_
  · rintro ⟨L, R⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_Omega] at h
    obtain ⟨⟨hL, iL⟩, ⟨hR, iR⟩⟩ := h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_Omega, Finset.mem_insert_self, and_true]
    refine ⟨fun x hx => ?_, fun x hx hx1 => ?_⟩
    · rw [Finset.mem_Ioo]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · omega
      rcases Finset.mem_union.1 hx with hx | hx
      · have := Finset.mem_Ioo.1 (hL hx); omega
      · have := Finset.mem_Ioo.1 (hR hx); omega
    · rcases Finset.mem_insert.1 hx with rfl | hx <;>
      rcases Finset.mem_insert.1 hx1 with h1 | h1
      · omega
      · rcases Finset.mem_union.1 h1 with h1 | h1
        · have := Finset.mem_Ioo.1 (hL h1); omega
        · have := Finset.mem_Ioo.1 (hR h1); omega
      · rcases Finset.mem_union.1 hx with hx | hx
        · have := Finset.mem_Ioo.1 (hL hx); omega
        · have := Finset.mem_Ioo.1 (hR hx); omega
      · rcases Finset.mem_union.1 hx with hx | hx <;>
        rcases Finset.mem_union.1 h1 with h1 | h1
        · exact iL x hx h1
        · have := Finset.mem_Ioo.1 (hL hx); have := Finset.mem_Ioo.1 (hR h1); omega
        · have := Finset.mem_Ioo.1 (hR hx); have := Finset.mem_Ioo.1 (hL h1); omega
        · exact iR x hx h1
  · intro E h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_Omega] at h
    obtain ⟨⟨hE, iE⟩, hp⟩ := h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_Omega]
    refine ⟨⟨fun x hx => ?_, fun x hx hx1 => iE x (Finset.mem_filter.1 hx).1
      (Finset.mem_filter.1 hx1).1⟩, ⟨fun x hx => ?_, fun x hx hx1 => iE x
      (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx1).1⟩⟩
    · obtain ⟨hxE, hxp⟩ := Finset.mem_filter.1 hx
      have := Finset.mem_Ioo.1 (hE hxE)
      have : x + 1 ≠ p := fun h => iE x hxE (h ▸ hp)
      rw [Finset.mem_Ioo]; omega
    · obtain ⟨hxE, hxp⟩ := Finset.mem_filter.1 hx
      have := Finset.mem_Ioo.1 (hE hxE)
      have : p + 1 ≠ x := fun h => iE p hp (h ▸ hxE)
      rw [Finset.mem_Ioo]; omega
  · rintro ⟨L, R⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_Omega] at h
    obtain ⟨⟨hL, -⟩, ⟨hR, -⟩⟩ := h
    simp only [Prod.mk.injEq]
    constructor
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h | h | h, hx⟩
        · omega
        · exact h
        · have := Finset.mem_Ioo.1 (hR h); omega
      · intro h; have := Finset.mem_Ioo.1 (hL h); exact ⟨Or.inr (Or.inl h), by omega⟩
    · ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨h | h | h, hx⟩
        · omega
        · have := Finset.mem_Ioo.1 (hL h); omega
        · exact h
      · intro h; have := Finset.mem_Ioo.1 (hR h); exact ⟨Or.inr (Or.inr h), by omega⟩
  · intro E h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨h1, -⟩ | ⟨h1, -⟩)
      · exact h.2
      · exact h1
      · exact h1
    · intro hx
      rcases lt_trichotomy x p with h1 | h1 | h1
      · exact Or.inr (Or.inl ⟨hx, h1⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨hx, h1⟩)

/-- **Fibonacci form**: `#{E ∈ Ω : p ∈ E} = f(p-a-2) · f(M-p-2)` with `f` the path count. -/
theorem forced_count_fib {a M p : ℕ} (hap : a < p) (hpM : p < M) :
    ((Omega a M).filter (fun E => p ∈ E)).card =
      indepCount (p - a - 2) * indepCount (M - p - 2) := by
  rw [forced_count_eq hap hpM, Ptot_eq_indepCount, Ptot_eq_indepCount]
  congr 2; omega

/-- **Exact prime resonance in Fibonacci form** on `0 < a < p < M < 2p`:
`A_p(T) = p · f(p-a-2) f(M-p-2) - f(M-a-1)`. -/
theorem prime_resonance_fib {a M p : ℕ} (hp : p.Prime) (ha : 0 < a) (hap : a < p) (hpM : p < M)
    (hM : M < 2 * p) :
    Acond (Omega a M) (Bz a M) (T a M ∅) (W a M ∅) p =
      (p : ℂ) * ((indepCount (p - a - 2) * indepCount (M - p - 2) : ℕ) : ℂ)
        - (indepCount (M - a - 1) : ℂ) := by
  rw [physical_prime_resonance hp ha hap hpM hM, forced_count_fib hap hpM, Ptot_eq_indepCount]

/-- **Forced-set density**: `P ≤ 8 · #{E ∈ Ω : p ∈ E}` for `a < p < M`.  (The map
`E ↦ insert p (E \ {p-1, p, p+1})` lands in the forced sets and is at most `8`-to-`1`.) -/
theorem Ptot_le_eight_forced {a M p : ℕ} (hap : a < p) (hpM : p < M) :
    Ptot a M ≤ 8 * ((Omega a M).filter (fun E => p ∈ E)).card := by
  classical
  set Z : Finset ℕ := {p - 1, p, p + 1}
  let f : Finset ℕ → Finset ℕ := fun E => insert p (E \ Z)
  have hmaps : ∀ E ∈ Omega a M, f E ∈ (Omega a M).filter (fun E => p ∈ E) := by
    intro E hE
    obtain ⟨hEs, hEi⟩ := mem_Omega.1 hE
    rw [Finset.mem_filter, mem_Omega]
    refine ⟨⟨fun x hx => ?_, fun x hx hx1 => ?_⟩, Finset.mem_insert_self _ _⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_Ioo.2 ⟨hap, hpM⟩
      · exact hEs (Finset.mem_sdiff.1 hx).1
    · rcases Finset.mem_insert.1 hx with rfl | hx <;>
      rcases Finset.mem_insert.1 hx1 with h1 | h1
      · omega
      · exact (Finset.mem_sdiff.1 h1).2 (by simp [Z])
      · have := (Finset.mem_sdiff.1 hx).2
        exact this (by simp [Z]; omega)
      · exact hEi x (Finset.mem_sdiff.1 hx).1 (Finset.mem_sdiff.1 h1).1
  have hfib : ∀ F ∈ (Omega a M).image f,
      ((Omega a M).filter (fun E => f E = F)).card ≤ 8 := by
    intro F _
    have hsub : (Omega a M).filter (fun E => f E = F) ⊆
        Z.powerset.image (fun S => (F \ Z) ∪ S) := by
      intro E hE
      obtain ⟨-, hEF⟩ := Finset.mem_filter.1 hE
      rw [Finset.mem_image]
      refine ⟨E ∩ Z, Finset.mem_powerset.2 Finset.inter_subset_right, ?_⟩
      rw [← hEF]
      ext x
      simp only [f, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter]
      by_cases hx : x ∈ Z
      · simp [hx]
      · have hxp : x ≠ p := fun h => hx (by simp [Z, h])
        simp [hx, hxp]
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_powerset]
    exact (Nat.pow_le_pow_right (by norm_num) Finset.card_le_three).trans (by norm_num)
  have h1 := Finset.card_le_mul_card_image (Omega a M) 8 hfib
  have h2 : (Omega a M).image f ⊆ (Omega a M).filter (fun E => p ∈ E) := by
    intro F hF
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hF
    exact hmaps E hE
  rw [Ptot]
  exact h1.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card h2))

end Erdos287.PostQSigma
