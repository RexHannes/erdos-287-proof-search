import RequestProject.Erdos287.ResearchBankV22.SmallPrimeUpperSieve

/-!
# Erdős #287 — Research Bank V22 §6: the completed positive upper-sieve weight

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `conv f g A = ∑_{B ⊆ A} f(B) g(A \ B)` — Dirichlet convolution of squarefree-supported weights
  (in the atom-set model a product `bc` of squarefree moduli with DISJOINT atom sets);
* `muE E A = μ(A) · 1_{A ⊆ E}` — `μ_E(e) = μ(e) · 1(e ∣ P_E)`;
* `completedWeight E β ℓ = μ_E ⋆ β ⋆ ℓ` — **the completed weight `Λ_new^+`**, instantiated
  (`LambdaNewPlus`) with the ACTUAL Rosser weight `β_sm^+` (§5) and the ACTUAL rounded rough
  weight `ℓ_rd` (§3).

Kernel-proved (LEAN BANK):
* `dsum_conv_eq`, **`dsum_conv_disjoint`** — for weights on disjoint prime universes
  `S_{f⋆g} = S_f · S_g`;
* `dsum_muE` — `S_{μ_E}(n) = 1(gcd(n, P_E) = 1)` (Möbius tail);
* **`dsum_completed_eq`** — `S_Λ(n) = 1(gcd(n,P_E)=1) · S_β(n) · S_ℓ(n)`;
* **`dsum_completed_nonneg`** — `S_Λ(n) ≥ 0`;
* **`dsum_completed_ge_survivor`** — `S_Λ(n) ≥ 1(n survives the entire auxiliary sieve)`;
* `LambdaNewPlus_nonneg`, `LambdaNewPlus_ge_survivor` — the same for the concrete `Λ_new^+`;
* `natDivSum_lift` — transfer to genuine divisor sums over `ℕ`:
  `∑_{d ∣ n} Λ(d) = S_Λ({p ∈ U : p ∣ n})`, and `natDivSum_LambdaNewPlus`;
* **`completed_support_budget`** — every modulus in the support of `Λ_new^+` satisfies
  `d ≤ P_E · level · X`, i.e. `P_E · x^{rho} · x^{vartheta0} = P_E · x^{vartheta}`.  The fixed
  factor `P_E` is kept explicitly (never set to `1`, never absorbed into `W0`).
-/

namespace Erdos287
namespace ResearchBankV22
namespace CompletedPositiveWeight

open Finset RoundedRoughSieve FirstForbiddenPrefix SmallPrimeUpperSieve

section Generic

variable {γ : Type*} [DecidableEq γ]

/-- Dirichlet convolution of squarefree-supported weights. -/
def conv (f g : Finset γ → ℝ) (A : Finset γ) : ℝ := ∑ B ∈ A.powerset, f B * g (A \ B)

theorem dsum_conv_eq (f g : Finset γ → ℝ) (D : Finset γ) :
    dsum (conv f g) D = ∑ B ∈ D.powerset, f B * dsum g (D \ B) := by
  unfold dsum conv
  rw [Finset.sum_comm' (t' := D.powerset) (s' := fun B => D.powerset.filter (B ⊆ ·))]
  · refine sum_congr rfl fun B hB => ?_
    rw [mul_sum]
    refine sum_nbij' (fun A => A \ B) (fun C => C ∪ B) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      rw [mem_filter, mem_powerset] at hA
      rw [mem_powerset]
      exact sdiff_subset_sdiff hA.1 (Subset.refl B)
    · intro C hC
      rw [mem_powerset] at hC
      rw [mem_filter, mem_powerset]
      exact ⟨union_subset (hC.trans sdiff_subset) (mem_powerset.1 hB), subset_union_right⟩
    · intro A hA
      rw [mem_filter, mem_powerset] at hA
      exact sdiff_union_of_subset hA.2
    · intro C hC
      rw [mem_powerset] at hC
      refine union_sdiff_cancel_right ?_
      exact disjoint_of_subset_left hC sdiff_disjoint
    · intro A _; rfl
  · intro A B
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨hA, hB⟩; exact ⟨⟨hA, hB⟩, hB.trans hA⟩
    · rintro ⟨⟨hA, hB⟩, -⟩; exact ⟨hA, hB⟩

/-- **Disjoint prime universes factor the divisor sum**: `S_{f⋆g} = S_f · S_g`. -/
theorem dsum_conv_disjoint {f g : Finset γ → ℝ} {U1 U2 : Finset γ} (hf : SupportedIn f U1)
    (hg : SupportedIn g U2) (hd : Disjoint U1 U2) (D : Finset γ) :
    dsum (conv f g) D = dsum f D * dsum g D := by
  rw [dsum_conv_eq]
  unfold dsum
  rw [sum_mul]
  refine sum_congr rfl fun B _ => ?_
  by_cases hB : f B = 0
  · simp [hB]
  congr 1
  have hBU := hf B hB
  change dsum g (D \ B) = dsum g D
  rw [dsum_inter hg, dsum_inter hg D]
  congr 1
  ext p
  simp only [mem_inter, mem_sdiff]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun h => disjoint_left.1 hd (hBU h) h2⟩, h2⟩

/-- The support of a convolution lies in the union of the supports. -/
theorem conv_supported {f g : Finset γ → ℝ} {U1 U2 : Finset γ} (hf : SupportedIn f U1)
    (hg : SupportedIn g U2) : SupportedIn (conv f g) (U1 ∪ U2) := by
  intro A hA
  obtain ⟨B, hB, hne⟩ := exists_ne_zero_of_sum_ne_zero hA
  have h1 := hf B (left_ne_zero_of_mul hne)
  have h2 := hg _ (right_ne_zero_of_mul hne)
  intro p hp
  by_cases hpB : p ∈ B
  · exact mem_union_left _ (h1 hpB)
  · exact mem_union_right _ (h2 (mem_sdiff.2 ⟨hp, hpB⟩))

/-- `μ_E(A) = μ(A) · 1_{A ⊆ E}`. -/
noncomputable def muE (E : Finset γ) (A : Finset γ) : ℝ :=
  if A ⊆ E then (-1 : ℝ) ^ A.card else 0

theorem muE_supported (E : Finset γ) : SupportedIn (muE E) E := by
  intro A hA; by_contra h; exact hA (by simp [muE, h])

/-- `S_{μ_E}(D) = 1(D ∩ E = ∅)` — i.e. `1(gcd(n, P_E) = 1)`. -/
theorem dsum_muE (E D : Finset γ) : dsum (muE E) D = if D ∩ E = ∅ then 1 else 0 := by
  rw [dsum_inter (muE_supported E), ← mobius_tail]
  unfold dsum
  refine sum_congr rfl fun A hA => ?_
  simp [muE, (mem_powerset.1 hA).trans inter_subset_right]

/-- **The completed weight** `Λ = μ_E ⋆ β ⋆ ℓ`. -/
noncomputable def completedWeight (E : Finset γ) (β ℓ : Finset γ → ℝ) : Finset γ → ℝ :=
  conv (conv (muE E) β) ℓ

variable {E Psm Prd : Finset γ} {β ℓ : Finset γ → ℝ}

/-- **Factorization of the completed divisor sum**
`S_Λ(n) = 1(gcd(n,P_E)=1) · S_β(n) · S_ℓ(n)` (three disjoint prime universes). -/
theorem dsum_completed_eq (hβ : SupportedIn β Psm) (hℓ : SupportedIn ℓ Prd)
    (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd) (D : Finset γ) :
    dsum (completedWeight E β ℓ) D = (if D ∩ E = ∅ then 1 else 0) * dsum β D * dsum ℓ D := by
  unfold completedWeight
  rw [dsum_conv_disjoint (conv_supported (muE_supported E) hβ) hℓ
      (disjoint_union_left.2 ⟨h2, h3⟩),
    dsum_conv_disjoint (muE_supported E) hβ h1, dsum_muE]

/-- **Positivity** `S_Λ(n) ≥ 0`. -/
theorem dsum_completed_nonneg (hβ : SupportedIn β Psm) (hℓ : SupportedIn ℓ Prd)
    (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd)
    (hβ0 : ∀ D, 0 ≤ dsum β D) (hℓ0 : ∀ D, 0 ≤ dsum ℓ D) (D : Finset γ) :
    0 ≤ dsum (completedWeight E β ℓ) D := by
  rw [dsum_completed_eq hβ hℓ h1 h2 h3]
  exact mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (hβ0 D)) (hℓ0 D)

/-- **Upper-sieve property** `S_Λ(n) ≥ 1(n survives the entire auxiliary sieve)`. -/
theorem dsum_completed_ge_survivor (hβ : SupportedIn β Psm) (hℓ : SupportedIn ℓ Prd)
    (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd)
    (hβu : ∀ D, (if D ∩ Psm = ∅ then 1 else 0) ≤ dsum β D)
    (hℓu : ∀ D, (if D ∩ Prd = ∅ then 1 else 0) ≤ dsum ℓ D) (D : Finset γ) :
    (if D ∩ (E ∪ Psm ∪ Prd) = ∅ then 1 else 0) ≤ dsum (completedWeight E β ℓ) D := by
  have hβ0 : ∀ D, 0 ≤ dsum β D := fun D => le_trans (by split_ifs <;> norm_num) (hβu D)
  have hℓ0 : ∀ D, 0 ≤ dsum ℓ D := fun D => le_trans (by split_ifs <;> norm_num) (hℓu D)
  split_ifs with hs
  · rw [dsum_completed_eq hβ hℓ h1 h2 h3]
    have hE : D ∩ E = ∅ := by
      rw [eq_empty_iff_forall_notMem] at hs ⊢
      intro p hp; exact hs p (by simp only [mem_inter, mem_union] at hp ⊢; tauto)
    have hS : D ∩ Psm = ∅ := by
      rw [eq_empty_iff_forall_notMem] at hs ⊢
      intro p hp; exact hs p (by simp only [mem_inter, mem_union] at hp ⊢; tauto)
    have hR : D ∩ Prd = ∅ := by
      rw [eq_empty_iff_forall_notMem] at hs ⊢
      intro p hp; exact hs p (by simp only [mem_inter, mem_union] at hp ⊢; tauto)
    have a := hβu D; have b := hℓu D
    rw [if_pos hS] at a; rw [if_pos hR] at b
    rw [if_pos hE, one_mul]
    nlinarith
  · exact dsum_completed_nonneg hβ hℓ h1 h2 h3 hβ0 hℓ0 D

end Generic

/-! ### The concrete completed weight `Λ_new^+` on actual primes -/

/-- **`Λ_new^+ = μ_E ⋆ β_sm^+ ⋆ ℓ_rd`** with the actual Rosser small weight at level `level`
(`= x^rho`) and the actual rounded rough weight at level `X` (`= x^{vartheta0}`). -/
noncomputable def LambdaNewPlus (E Psm Prd : Finset ℕ) (level : ℝ) (w : ℕ → ℝ) (X : ℝ) :
    Finset ℕ → ℝ :=
  completedWeight E (rosserBeta Psm level) (ellRd Prd w X)

section Concrete

variable {E Psm Prd : Finset ℕ} {level X : ℝ} {w : ℕ → ℝ}

theorem LambdaNewPlus_nonneg (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd)
    (D : Finset ℕ) : 0 ≤ dsum (LambdaNewPlus E Psm Prd level w X) D :=
  dsum_completed_nonneg (ellRd_supported _ _ _) (ellRd_supported _ _ _) h1 h2 h3
    (dsum_ellRd_nonneg _ _ _) (dsum_ellRd_nonneg _ _ _) D

theorem LambdaNewPlus_ge_survivor (h1 : Disjoint E Psm) (h2 : Disjoint E Prd)
    (h3 : Disjoint Psm Prd) (D : Finset ℕ) :
    (if D ∩ (E ∪ Psm ∪ Prd) = ∅ then 1 else 0) ≤ dsum (LambdaNewPlus E Psm Prd level w X) D :=
  dsum_completed_ge_survivor (ellRd_supported _ _ _) (ellRd_supported _ _ _) h1 h2 h3
    (dsum_ellRd_ge _ _ _) (dsum_ellRd_ge _ _ _) D

theorem LambdaNewPlus_supported :
    SupportedIn (LambdaNewPlus E Psm Prd level w X) (E ∪ Psm ∪ Prd) :=
  conv_supported (conv_supported (muE_supported E) (ellRd_supported _ _ _))
    (ellRd_supported _ _ _)

end Concrete

/-! ### Transfer to genuine divisor sums over `ℕ` -/

/-- Lift of an atom-set weight on the prime universe `U` to an arithmetic function. -/
def liftN (U : Finset ℕ) (f : Finset ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ A ∈ U.powerset, if ∏ p ∈ A, p = d then f A else 0

/-- **Divisor-sum transfer**: `∑_{d ∣ n} (lift f)(d) = S_f({p ∈ U : p ∣ n})` for `n ≠ 0`. -/
theorem natDivSum_lift {U : Finset ℕ} (hU : ∀ p ∈ U, p.Prime) (f : Finset ℕ → ℝ) {n : ℕ}
    (hn : n ≠ 0) : ∑ d ∈ n.divisors, liftN U f d = dsum f (U.filter (· ∣ n)) := by
  unfold liftN
  rw [sum_comm]
  simp_rw [sum_ite_eq, Nat.mem_divisors]
  unfold dsum
  rw [← sum_filter]
  congr 1
  ext A
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hA, hd, -⟩ p hp
    exact mem_filter.2 ⟨hA hp, dvd_trans (dvd_prod_of_mem _ hp) hd⟩
  · intro hA
    refine ⟨hA.trans (filter_subset _ _), ?_, hn⟩
    exact prod_primes_dvd n (fun p hp => (hU p (mem_filter.1 (hA hp)).1).prime)
      (fun p hp => (mem_filter.1 (hA hp)).2)

/-- **`S_Λ(n)` as a genuine divisor sum** for the concrete completed weight. -/
theorem natDivSum_LambdaNewPlus {E Psm Prd : Finset ℕ} {level X : ℝ} {w : ℕ → ℝ}
    (hU : ∀ p ∈ E ∪ Psm ∪ Prd, p.Prime) (h1 : Disjoint E Psm) (h2 : Disjoint E Prd)
    (h3 : Disjoint Psm Prd) {n : ℕ} (hn : n ≠ 0) :
    (if ∀ p ∈ E ∪ Psm ∪ Prd, ¬ p ∣ n then 1 else 0) ≤
      ∑ d ∈ n.divisors, liftN (E ∪ Psm ∪ Prd) (LambdaNewPlus E Psm Prd level w X) d ∧
    0 ≤ ∑ d ∈ n.divisors, liftN (E ∪ Psm ∪ Prd) (LambdaNewPlus E Psm Prd level w X) d := by
  rw [natDivSum_lift hU _ hn]
  refine ⟨le_trans ?_ (LambdaNewPlus_ge_survivor h1 h2 h3 _), LambdaNewPlus_nonneg h1 h2 h3 _⟩
  split_ifs with ha hb hb
  · exact le_rfl
  · exfalso; apply hb
    rw [eq_empty_iff_forall_notMem]
    intro p hp
    simp only [mem_inter, mem_filter] at hp
    exact ha p hp.1.1 hp.1.2
  · exact zero_le_one
  · exact le_rfl

/-! ### Support budget `P_E · x^{rho} · x^{vartheta0}` -/

/-- **Support budget**: every modulus in the support of `Λ_new^+` has size at most
`P_E · level · X` (`= P_E · x^{rho + vartheta0} = P_E · x^{vartheta}`). -/
theorem completed_support_budget {E Psm Prd : Finset ℕ} {level X : ℝ} {w : ℕ → ℝ}
    (hE : ∀ p ∈ E, 1 ≤ p) (hPsm : ∀ p ∈ Psm, 1 ≤ p) (hlev : 1 ≤ level) (hX : 1 ≤ X)
    (hwp : ∀ p ∈ Prd, (p : ℝ) ≤ w p) (hw1 : ∀ p ∈ Prd, 1 ≤ w p)
    (hmono : ∀ p ∈ Prd, ∀ q ∈ Prd, p ≤ q → w p ≤ w q) {A : Finset ℕ}
    (hA : LambdaNewPlus E Psm Prd level w X A ≠ 0) :
    (∏ p ∈ A, (p : ℝ)) ≤ (∏ p ∈ E, (p : ℝ)) * level * X := by
  unfold LambdaNewPlus completedWeight conv at hA
  obtain ⟨B, hB, hne⟩ := exists_ne_zero_of_sum_ne_zero hA
  have hB1 := left_ne_zero_of_mul hne
  have hB2 := right_ne_zero_of_mul hne
  obtain ⟨C, hC, hne'⟩ := exists_ne_zero_of_sum_ne_zero hB1
  have hC1 := left_ne_zero_of_mul hne'
  have hC2 := right_ne_zero_of_mul hne'
  have hBA := mem_powerset.1 hB
  have hCB := mem_powerset.1 hC
  have hCE : C ⊆ E := muE_supported E C hC1
  have hsm := (rosserSmallProvider Psm level hlev hPsm).level_supp (B \ C) hC2
  have hRd : A \ B ⊆ Prd := ellRd_supported Prd w X _ hB2
  have hrd : (∏ p ∈ A \ B, w p) ≤ X := by
    unfold ellRd at hB2
    rw [if_pos hRd] at hB2
    unfold ellW at hB2
    split_ifs at hB2 with hadm
    · exact ellW_support_prod_le hX (fun p hp => hw1 p (hRd hp))
        (fun p hp q hq h => hmono p (hRd hp) q (hRd hq) h) hadm
    · exact absurd rfl hB2
  have hrd' : (∏ p ∈ A \ B, (p : ℝ)) ≤ X :=
    le_trans (prod_le_prod (fun p _ => Nat.cast_nonneg p) (fun p hp => hwp p (hRd hp))) hrd
  have hEC : (∏ p ∈ C, (p : ℝ)) ≤ ∏ p ∈ E, (p : ℝ) := by
    have : ∏ p ∈ C, p ≤ ∏ p ∈ E, p :=
      prod_le_prod_of_subset_of_one_le' hCE (fun p hp _ => hE p hp)
    have h' : ((∏ p ∈ C, p : ℕ) : ℝ) ≤ ((∏ p ∈ E, p : ℕ) : ℝ) := by exact_mod_cast this
    simpa only [Nat.cast_prod] using h'
  rw [← prod_sdiff hBA, ← prod_sdiff hCB]
  have p1 : 0 ≤ ∏ p ∈ C, (p : ℝ) := prod_nonneg fun p _ => Nat.cast_nonneg p
  have p2 : 0 ≤ ∏ p ∈ B \ C, (p : ℝ) := prod_nonneg fun p _ => Nat.cast_nonneg p
  have p3 : 0 ≤ ∏ p ∈ A \ B, (p : ℝ) := prod_nonneg fun p _ => Nat.cast_nonneg p
  calc (∏ p ∈ A \ B, (p : ℝ)) * ((∏ p ∈ B \ C, (p : ℝ)) * ∏ p ∈ C, (p : ℝ))
      ≤ X * (level * ∏ p ∈ E, (p : ℝ)) := by
        apply mul_le_mul hrd' (mul_le_mul hsm hEC p1 (by linarith)) (by positivity)
          (by linarith)
    _ = (∏ p ∈ E, (p : ℝ)) * level * X := by ring

end CompletedPositiveWeight
end ResearchBankV22
end Erdos287
