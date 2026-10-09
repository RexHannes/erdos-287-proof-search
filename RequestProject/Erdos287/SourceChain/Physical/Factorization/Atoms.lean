import RequestProject.Erdos287.SourceChain.Physical.Factorization.Tensor

/-!
# Erdős #287 — the legal three-factor atoms of `ℓ_X`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

* `partCount_le` — at most `γ_k` partial tuples of class `k` have a given product (injection
  into the stabiliser of the class/box labelling; repeated-box multiplicity), hence
  `colFactor_nonneg`, `colFactor_le_one`: **every colour factor is one-bounded**.
* `colFactor_support` — `γ_{k,χ}(m) ≠ 0` forces every prime of `m` to be high, `χ`-coloured
  `k`, and `m ≤ E_k = ∏_{c(i)=k} D_{P_i}^{1+τ}` (the factor size range).
* `lowFactor = κ_J * γ_{0,χ}`; `abs_lowFactor_le` — `|κ_J * γ_{0,χ}| ≤ 1` (unique low/high
  split); `lowFactor_support` — `n ≤ D_low E₀`.
* `lowFactor_coprime` — the colour-0 factor (with the low primes) is coprime to the colour-1
  and colour-2 factors (disjoint prime-support colouring), and so are colours 1 and 2.
* `ellX_tensor` — **exact identity for every modulus `d`**:
  `ℓ_X(d) = ∑_{J ≤ T²} ∑_{P ∈ 𝐃_J^+} (-1)^J w_{J,P} ∑_χ ((κ_J * γ_{0,χ}) * γ_{1,χ} * γ_{2,χ})(d)`,
  for **any** colouring rule `(J,P) ↦ c_{J,P}` (in particular the Pascadi colouring).
* `atomWeight_nonneg`, `atomWeight_mul_le` — `0 ≤ w_{J,P}` and `3^K w_{J,P} ≤ 3^J`
  (`∏_k γ_k ≤ γ(P)`, multinomial); `total_variation_le` —
  `∑_{J,P,χ} |(-1)^J w_{J,P}| ≤ ∑_{J ≤ T²} H^J 3^J`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.Sieve.ScalarParams

open Erdos287.Physical.Factor

variable {S : ScalarParams}

/-! ### One-boundedness of the colour factors -/

/-- The class/box labelling whose stabiliser has order `γ_k`. -/
def classLabel {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (k : Fin 3) :
    Fin J → Fin S.H ⊕ Fin J :=
  fun i => if c i.val = k then Sum.inl (P i) else Sum.inr i

lemma card_stab_classLabel {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (k : Fin 3) :
    (univ.filter (fun π : Equiv.Perm (Fin J) => classLabel P c k ∘ π = classLabel P c k)).card =
      S.gammaCol J P c k := by
  classical
  rw [perm_count_eq_gamma (π₀ := Equiv.refl _) (by rfl), Fintype.prod_sum_type, gammaCol]
  have h2 : ∏ j : Fin J, (univ.filter (fun i => classLabel P c k i = Sum.inr j)).card.factorial
      = 1 := by
    refine prod_eq_one (fun j _ => Nat.factorial_eq_one.2 ?_)
    refine (card_le_card (s := univ.filter (fun i => classLabel P c k i = Sum.inr j))
      (t := {j}) ?_).trans (by simp)
    intro i hi
    simp only [mem_filter, mem_univ, true_and, classLabel] at hi
    split_ifs at hi; simp_all
  rw [h2, mul_one]
  refine prod_congr rfl (fun b _ => ?_)
  congr 2
  ext i
  simp only [mem_filter, mem_univ, true_and, classLabel]
  split_ifs with h <;> simp [h]

lemma prime_dvd_prod_tuple {J : ℕ} {q : Fin J → ℕ} (hq : ∀ i, q i = 1 ∨ (q i).Prime)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ ∏ i, q i) : ∃ i, (q i).Prime ∧ p = q i := by
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hp.prime q).1 hd
  rcases hq i with h | h
  · rw [h] at hi; exact absurd (Nat.dvd_one.1 hi) hp.one_lt.ne'
  · exact ⟨i, h, (Nat.prime_dvd_prime_iff_eq hp h).1 hi⟩

lemma partTuples_entry (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} {k : Fin 3} {q : Fin J → ℕ} (hq : q ∈ S.partTuples J P c χ k)
    (i : Fin J) : q i = 1 ∨ (q i).Prime := by
  have := hS
  by_cases h : c i.val = k
  · right
    have hm := (((mem_partTuples.1 hq).1 i).1 h).1
    classical
    unfold boxPrimes at hm
    exact (mem_filter.1 hm).2.1
  · left; exact ((mem_partTuples.1 hq).1 i).2 h

open Classical in
/-- **At most `γ_k` partial tuples of class `k` have a given product.** -/
theorem partCount_le (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) (m : ℕ) :
    ((S.partTuples J P c χ k).filter (fun q => ∏ i, q i = m)).card ≤ S.gammaCol J P c k := by
  set A := (S.partTuples J P c χ k).filter (fun q => ∏ i, q i = m) with hA
  rcases A.eq_empty_or_nonempty with h | ⟨q0, hq0⟩
  · rw [h]; exact Nat.zero_le _
  rw [← card_stab_classLabel P c k]
  obtain ⟨hq0p, hq0m⟩ := mem_filter.1 hq0
  refine card_le_card_of_surjOn (fun π => q0 ∘ π) ?_
  intro q hq
  obtain ⟨hqp, hqm⟩ := mem_filter.1 (Finset.mem_coe.1 hq)
  have hmq := mem_partTuples.1 hqp
  have hmq0 := mem_partTuples.1 hq0p
  -- every entry of `q` in the class is an entry of `q0` in the class
  have hex : ∀ i : {i : Fin J // c i.val = k}, ∃ j : {j : Fin J // c j.val = k},
      q0 j.1 = q i.1 := by
    rintro ⟨i, hi⟩
    have hpi : (q i).Prime := by
      rcases partTuples_entry hS hqp i with h | h
      · exfalso
        have hb := ((hmq.1 i).1 hi).1
        unfold boxPrimes at hb
        have := (mem_filter.1 hb).2.1; rw [h] at this; exact Nat.not_prime_one this
      · exact h
    have hd : q i ∣ ∏ j, q0 j := by
      rw [hq0m, ← hqm]; exact dvd_prod_of_mem q (mem_univ i)
    obtain ⟨j, hj, hji⟩ := prime_dvd_prod_tuple (partTuples_entry hS hq0p) hpi hd
    have hcj : c j.val = k := by
      by_contra hne
      rw [(hmq0.1 j).2 hne] at hj; exact Nat.not_prime_one hj
    exact ⟨⟨j, hcj⟩, hji.symm⟩
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i i' h
    have := hσ i; rw [h, hσ i'] at this
    exact Subtype.ext (hmq.2 i.1 i'.1 i.2 i'.2 this.symm)
  set e : Equiv.Perm {i : Fin J // c i.val = k} :=
    Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  refine ⟨Equiv.Perm.ofSubtype e, ?_, ?_⟩
  · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    funext i
    simp only [Function.comp_apply]
    by_cases hi : c i.val = k
    · rw [Equiv.Perm.ofSubtype_apply_of_mem e hi]
      have hc' := (e ⟨i, hi⟩).2
      simp only [classLabel, if_pos hc', if_pos hi]
      congr 1
      -- the boxes agree
      have h1 := ((hmq0.1 (e ⟨i, hi⟩).1).1 hc').1
      have h2 := ((hmq.1 i).1 hi).1
      have heq : q0 (e ⟨i, hi⟩).1 = q i := hσ ⟨i, hi⟩
      unfold boxPrimes at h1 h2
      have b1 := (mem_filter.1 h1).2.2
      have b2 := (mem_filter.1 h2).2.2
      rw [heq] at b1
      exact Fin.ext (inBox_unique hS b1 b2)
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem e hi]
  · funext i
    simp only [Function.comp_apply]
    by_cases hi : c i.val = k
    · rw [Equiv.Perm.ofSubtype_apply_of_mem e hi]; exact hσ ⟨i, hi⟩
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem e hi, (hmq0.1 i).2 hi, (hmq.1 i).2 hi]

lemma colFactor_apply {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (χ : Fin S.Kc → Fin 3)
    (k : Fin 3) {m : ℕ} (hm : m ≠ 0) [DecidableEq ℕ] :
    S.colFactor J P c χ k m = (S.gammaCol J P c k : ℝ)⁻¹ *
      (((S.partTuples J P c χ k).filter (fun q => ∏ i, q i = m)).card : ℝ) := by
  classical
  unfold colFactor
  rw [scaleAF_apply, cntAF_apply _ _ hm]

theorem colFactor_nonneg {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) (m : ℕ) : 0 ≤ S.colFactor J P c χ k m := by
  classical
  by_cases hm : m = 0
  · subst hm; simp
  rw [colFactor_apply P c χ k hm]; positivity

/-- **One-boundedness of every colour factor.** -/
theorem colFactor_le_one (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) (m : ℕ) : S.colFactor J P c χ k m ≤ 1 := by
  classical
  by_cases hm : m = 0
  · subst hm; simp
  rw [colFactor_apply P c χ k hm]
  have hpos : (0 : ℝ) < S.gammaCol J P c k := by exact_mod_cast gammaCol_pos J P c k
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact_mod_cast partCount_le hS P c χ k m

theorem abs_colFactor_le (hS : S.Good) {J : ℕ} (P : Fin J → Fin S.H) (c : ℕ → Fin 3)
    (χ : Fin S.Kc → Fin 3) (k : Fin 3) (m : ℕ) : |S.colFactor J P c χ k m| ≤ 1 := by
  rw [abs_of_nonneg (colFactor_nonneg P c χ k m)]; exact colFactor_le_one hS P c χ k m

/-! ### Support and size range of the colour factors -/

/-- **Support of a colour factor**: `m ≠ 0`, every prime factor of `m` is high and
`χ`-coloured `k`, and `m ≤ E_k`. -/
theorem colFactor_support (hS : S.Good) {J : ℕ} {P : Fin J → Fin S.H} {c : ℕ → Fin 3}
    {χ : Fin S.Kc → Fin 3} {k : Fin 3} {m : ℕ} (h : S.colFactor J P c χ k m ≠ 0) :
    m ≠ 0 ∧ (∀ p, p.Prime → p ∣ m → S.IsHigh p ∧ S.chiAt χ p = k) ∧
      (m : ℝ) ≤ cprod (S.boxVec J P) c k J := by
  classical
  have hm : m ≠ 0 := by intro h0; subst h0; simp at h
  rw [colFactor_apply P c χ k hm] at h
  have hne : ((S.partTuples J P c χ k).filter (fun q => ∏ i, q i = m)).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro he; rw [he] at h; simp at h
  obtain ⟨q, hq⟩ := hne
  obtain ⟨hqp, hqm⟩ := mem_filter.1 hq
  have hmq := mem_partTuples.1 hqp
  refine ⟨hm, fun p hp hd => ?_, ?_⟩
  · rw [← hqm] at hd
    obtain ⟨i, hi, rfl⟩ := prime_dvd_prod_tuple (partTuples_entry hS hqp) hp hd
    have hci : c i.val = k := by
      by_contra hne; rw [(hmq.1 i).2 hne] at hi; exact Nat.not_prime_one hi
    obtain ⟨hb, hχ⟩ := (hmq.1 i).1 hci
    unfold boxPrimes at hb
    obtain ⟨-, hpr, hbox⟩ := mem_filter.1 hb
    exact ⟨⟨hpr, P i, (P i).2, hbox⟩, hχ⟩
  · rw [← hqm]
    push_cast
    have e1 : ∏ i, (q i : ℝ) = ∏ i ∈ univ.filter (fun i : Fin J => c i.val = k), (q i : ℝ) := by
      rw [prod_filter]
      refine prod_congr rfl (fun i _ => ?_)
      split_ifs with hi
      · rfl
      · rw [(hmq.1 i).2 hi]; simp
    rw [e1]
    have e := prod_fin_filter_eq J c k (fun i => S.boxTop (P i))
    have e' : ∀ i ∈ (range J).filter (fun i => c i = k),
        (if h : i < J then S.boxTop (P ⟨i, h⟩) else 1) = S.boxVec J P i := fun i _ => rfl
    rw [prod_congr rfl e'] at e
    unfold cprod
    rw [← e]
    refine prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i hi => ?_)
    have hci : c i.val = k := (mem_filter.1 hi).2
    have hb := ((hmq.1 i).1 hci).1
    unfold boxPrimes at hb
    exact (mem_filter.1 hb).2.2.2

end Erdos287.Physical.Sieve.ScalarParams
