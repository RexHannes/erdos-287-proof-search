import RequestProject.Erdos287.SourceChain.Physical.TypeII.HeathBrown

/-!
# Erdős #287 — Type-II source: dyadic Heath–Brown cells and the coefficients `α_n`, `β_m`

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Following Maynard (arXiv:2006.07088v1, proof of Theorem 1.1 after Lemma 5.3): apply
`heathBrown_three`, keep the roughness condition `P^-(n) ≥ z₀`, and put each of the six variables
`n_1, n_2, n_3, m_1, m_2, m_3` into a dyadic interval `[2^e, 2^{e+1})`.

* `hbVar j i` — the six variable sequences of the `j`-th Heath–Brown term (`j = 1,2,3`):
  `n_1 ↦ log n_1`, `n_2, n_3 ↦ 1`, `m_1, m_2, m_3 ↦ μ(m) 1_{m ≤ z}`; unused variables are the
  Dirichlet unit `δ`;
* `hbTerm j = ∏_i hbVar j i` and `hbTerm_eq` — this is `log * ζ^{j-1} * M_z^j`;
* `rough z₀`, `roughVar` — the roughness indicator `1_{P^-(n) ≥ z₀}` inserted in every variable;
  `rough_mul_apply` — exact for rough `n` (`P^-` is completely multiplicative in this sense);
* `dy e f` — dyadic restriction; `cellSeq j z₀ e = ∏_i dy (e i) (roughVar z₀ (hbVar j i))`;
* `prod_eq_sum_cells` — exact dyadic decomposition for `n < 2^E`;
* `alphaSeq`, `betaSeq` — for a branch with critical variable `c`, `α = dy (e c) (var c)` and
  `β = ∏_{i ≠ c} dy (e i) (var i)`; `cellSeq_eq_alpha_mul_beta`;
* `abs_alpha_le` — `|α_n| ≤ 1 + log n`; `alpha_support` — `α_n ≠ 0 ⇒ 2^{e_c} ≤ n < 2^{e_c+1}`;
* `abs_betaSeq_le` — `|β_m| ≤ (1 + log m)^5 d_5(m)`; `divisorPow_le` — `d_k(m) ≤ τ(m)^{k-1}`.
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset ArithmeticFunction

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

/-- The six Heath–Brown variable sequences of the `j`-th term (`j ∈ {1,2,3}`), indexed by
`i : Fin 6 = (n_1, n_2, n_3, m_1, m_2, m_3)`. -/
noncomputable def hbVar (z : ℕ) (j : ℕ) (i : Fin 6) : ArithmeticFunction ℝ :=
  match i with
  | 0 => log
  | 1 => if 2 ≤ j then (ζ : ArithmeticFunction ℝ) else 1
  | 2 => if 3 ≤ j then (ζ : ArithmeticFunction ℝ) else 1
  | 3 => Mz z
  | 4 => if 2 ≤ j then Mz z else 1
  | 5 => if 3 ≤ j then Mz z else 1

/-- The `j`-th Heath–Brown convolution `∏_i hbVar j i`. -/
noncomputable def hbTerm (z j : ℕ) : ArithmeticFunction ℝ := ∏ i, hbVar z j i

theorem hbTerm_one (z : ℕ) : hbTerm z 1 = log * Mz z := by
  simp [hbTerm, Fin.prod_univ_succ, hbVar]

theorem hbTerm_two (z : ℕ) : hbTerm z 2 = log * (ζ : ArithmeticFunction ℝ) * Mz z ^ 2 := by
  simp [hbTerm, Fin.prod_univ_succ, hbVar]; ring

theorem hbTerm_three (z : ℕ) :
    hbTerm z 3 = log * (ζ : ArithmeticFunction ℝ) ^ 2 * Mz z ^ 3 := by
  simp [hbTerm, Fin.prod_univ_succ, hbVar]; ring

/-- **Heath–Brown in six-variable form**: for `n < (z+1)^3`,
`Λ(n) = 3 hbTerm₁(n) - 3 hbTerm₂(n) + hbTerm₃(n)`. -/
theorem heathBrown_cells (z : ℕ) {n : ℕ} (hn : n < (z + 1) ^ 3) :
    ArithmeticFunction.vonMangoldt n =
      3 * hbTerm z 1 n - 3 * hbTerm z 2 n + hbTerm z 3 n := by
  rw [hbTerm_one, hbTerm_two, hbTerm_three]
  exact heathBrown_three z hn

/-! ### Roughness -/

/-- `P^-(n) ≥ z₀`: every prime factor of `n` is at least `z₀`. -/
def Rough (z₀ n : ℕ) : Prop := ∀ p ∈ n.primeFactors, z₀ ≤ p

instance (z₀ n : ℕ) : Decidable (Rough z₀ n) := by unfold Rough; infer_instance

open Classical in
/-- Insert the roughness indicator `1_{P^-(n) ≥ z₀}` into a sequence. -/
noncomputable def roughVar (z₀ : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Rough z₀ n then f n else 0, by simp⟩

theorem roughVar_apply (z₀ : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    roughVar z₀ f n = if Rough z₀ n then f n else 0 := rfl

theorem rough_of_dvd {z₀ a n : ℕ} (hn : n ≠ 0) (ha : a ∣ n) (h : Rough z₀ n) : Rough z₀ a :=
  fun p hp => h p (Nat.primeFactors_mono ha hn hp)

theorem rough_mul {z₀ a b : ℕ} (ha : Rough z₀ a) (hb : Rough z₀ b) : Rough z₀ (a * b) := by
  intro p hp
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp at hp
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp at hp
  rw [Nat.primeFactors_mul ha0.ne' hb0.ne', Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact ha p hp
  · exact hb p hp

/-- For rough `n`, roughness can be inserted in both factors of a convolution. -/
theorem rough_mul_apply (z₀ : ℕ) (f g : ArithmeticFunction ℝ) {n : ℕ} (hn : Rough z₀ n) :
    (f * g) n = (roughVar z₀ f * roughVar z₀ g) n := by
  classical
  rw [mul_apply, mul_apply]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
  rw [roughVar_apply, roughVar_apply,
    if_pos (rough_of_dvd hn0 (Dvd.intro _ hmul) hn),
    if_pos (rough_of_dvd hn0 (Dvd.intro_left _ hmul) hn)]

/-- Roughness inserted in all factors of a finite convolution product, for rough `n`. -/
theorem rough_prod_apply {ι : Type*} (z₀ : ℕ) (s : Finset ι) (f : ι → ArithmeticFunction ℝ) :
    ∀ {n : ℕ}, Rough z₀ n → (∏ i ∈ s, f i) n = (∏ i ∈ s, roughVar z₀ (f i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n _; simp
  | insert a s ha ih =>
    intro n hn
    rw [Finset.prod_insert ha, Finset.prod_insert ha, rough_mul_apply z₀ _ _ hn, mul_apply,
      mul_apply]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have h2 : Rough z₀ x.2 := rough_of_dvd hn0 (Dvd.intro_left _ hmul) hn
    congr 1
    rw [roughVar_apply, if_pos h2, ih h2]

/-! ### Dyadic cells -/

open Classical in
/-- Dyadic restriction `f · 1_{[2^e, 2^{e+1})}`. -/
noncomputable def dy (e : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if 2 ^ e ≤ n ∧ n < 2 ^ (e + 1) then f n else 0, by simp⟩

theorem dy_apply (e : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    dy e f n = if 2 ^ e ≤ n ∧ n < 2 ^ (e + 1) then f n else 0 := rfl

open Classical in
/-- Truncation `f · 1_{n < 2^E}`. -/
noncomputable def truncE (E : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n < 2 ^ E then f n else 0, by simp⟩

theorem truncE_apply (E : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    truncE E f n = if n < 2 ^ E then f n else 0 := rfl

theorem truncE_eq_sum_dy (E : ℕ) (f : ArithmeticFunction ℝ) :
    truncE E f = ∑ e ∈ range E, dy e f := by
  ext n
  rw [sum_apply', truncE_apply]
  simp_rw [dy_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hE : n < 2 ^ E
  · rw [if_pos hE]
    -- exactly one dyadic block contains `n`
    have hlog : 2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1) :=
      ⟨Nat.pow_log_le_self 2 hn.ne', Nat.lt_pow_succ_log_self (by norm_num) n⟩
    have hmem : Nat.log 2 n ∈ range E := by
      rw [Finset.mem_range]
      by_contra h; push_neg at h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
      omega
    rw [Finset.sum_eq_single (Nat.log 2 n)]
    · rw [if_pos hlog]
    · intro e _ hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hne
      exact (Nat.log_eq_of_pow_le_of_lt_pow h1 h2).symm
    · intro h; exact absurd hmem h
  · rw [if_neg hE]
    refine (Finset.sum_eq_zero (fun e he => ?_)).symm
    rw [if_neg]
    rintro ⟨-, h2⟩
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Finset.mem_range.1 he)
    apply hE; calc n < 2 ^ (e + 1) := h2
      _ ≤ 2 ^ E := this

/-- Truncating every factor does not change a convolution product below `2^E`. -/
theorem prod_truncE_apply {ι : Type*} (E : ℕ) (s : Finset ι) (f : ι → ArithmeticFunction ℝ) :
    ∀ {n : ℕ}, n < 2 ^ E → (∏ i ∈ s, f i) n = (∏ i ∈ s, truncE E (f i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n _; simp
  | insert a s ha ih =>
    intro n hn
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_apply, mul_apply]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.1 hx
    have h1 : x.1 < 2 ^ E := lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      (Dvd.intro _ hmul)) hn
    have h2 : x.2 < 2 ^ E := lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
      (Dvd.intro_left _ hmul)) hn
    rw [truncE_apply, if_pos h1, ih h2]

/-- **Exact dyadic decomposition**: for `n < 2^E`,
`(∏_i f_i)(n) = ∑_{e ∈ [0,E)^6} (∏_i dy (e i) f_i)(n)`. -/
theorem prod_eq_sum_cells (E : ℕ) (f : Fin 6 → ArithmeticFunction ℝ) {n : ℕ} (hn : n < 2 ^ E) :
    (∏ i, f i) n = ∑ e ∈ Fintype.piFinset (fun _ : Fin 6 => range E), (∏ i, dy (e i) (f i)) n := by
  classical
  rw [prod_truncE_apply E univ f hn]
  simp_rw [truncE_eq_sum_dy]
  rw [Finset.prod_univ_sum, sum_apply']

/-- The cell sequence of a dyadic Heath–Brown cell (with roughness). -/
noncomputable def cellSeq (z z₀ j : ℕ) (e : Fin 6 → ℕ) : ArithmeticFunction ℝ :=
  ∏ i, dy (e i) (roughVar z₀ (hbVar z j i))

/-- **Rough Heath–Brown term as a sum of dyadic cells** (`n` rough, `n < 2^E`). -/
theorem hbTerm_eq_sum_cells (z z₀ j E : ℕ) {n : ℕ} (hr : Rough z₀ n) (hn : n < 2 ^ E) :
    hbTerm z j n = ∑ e ∈ Fintype.piFinset (fun _ : Fin 6 => range E), cellSeq z z₀ j e n := by
  unfold hbTerm cellSeq
  rw [rough_prod_apply z₀ univ _ hr, prod_eq_sum_cells E _ hn]

/-! ### Branch coefficients -/

/-- **`α_n`**: the critical variable `c` of the cell `e` of the `j`-th term. -/
noncomputable def alphaSeq (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) : ArithmeticFunction ℝ :=
  dy (e c) (roughVar z₀ (hbVar z j c))

/-- **`β_m`**: the convolution of the five complementary variables. -/
noncomputable def betaSeq (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) : ArithmeticFunction ℝ :=
  ∏ i ∈ univ.erase c, dy (e i) (roughVar z₀ (hbVar z j i))

theorem cellSeq_eq_alpha_mul_beta (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) :
    cellSeq z z₀ j e = alphaSeq z z₀ j e c * betaSeq z z₀ j e c := by
  unfold cellSeq alphaSeq betaSeq
  exact (Finset.mul_prod_erase univ (fun i => dy (e i) (roughVar z₀ (hbVar z j i)))
    (mem_univ c)).symm

theorem abs_hbVar_le (z j : ℕ) (i : Fin 6) (n : ℕ) : |hbVar z j i n| ≤ 1 + Real.log n := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hMz : |Mz z n| ≤ 1 := by
    rw [Mz_apply]; split_ifs
    · exact_mod_cast abs_moebius_le_one
    · simp
  have hζ : |(ζ : ArithmeticFunction ℝ) n| ≤ 1 := by
    rw [natCoe_apply, zeta_apply]; split_ifs <;> simp
  have h1 : |(1 : ArithmeticFunction ℝ) n| ≤ 1 := by
    rw [one_apply]; split_ifs <;> simp
  fin_cases i <;> simp only [hbVar] <;> (try split_ifs) <;>
    first
    | (rw [log_apply, abs_of_nonneg hlog]; linarith)
    | linarith

theorem abs_roughVar_le {z₀ : ℕ} {f : ArithmeticFunction ℝ} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : |f n| ≤ B) : |roughVar z₀ f n| ≤ B := by
  classical
  rw [roughVar_apply]; split_ifs
  · exact h
  · simpa using hB

theorem abs_dy_le {e : ℕ} {f : ArithmeticFunction ℝ} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : |f n| ≤ B) : |dy e f n| ≤ B := by
  rw [dy_apply]; split_ifs
  · exact h
  · simpa using hB

/-- **Coefficient bound** `|α_n| ≤ 1 + log n`. -/
theorem abs_alpha_le (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) (n : ℕ) :
    |alphaSeq z z₀ j e c n| ≤ 1 + Real.log n := by
  have h0 : 0 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  exact abs_dy_le h0 (abs_roughVar_le h0 (abs_hbVar_le z j c n))

/-- **Support** of `α`: the dyadic block `[2^{e_c}, 2^{e_c+1})`, and only rough `n`. -/
theorem alpha_support (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) {n : ℕ}
    (h : alphaSeq z z₀ j e c n ≠ 0) : 2 ^ e c ≤ n ∧ n < 2 ^ (e c + 1) ∧ Rough z₀ n := by
  classical
  unfold alphaSeq at h
  rw [dy_apply] at h
  split_ifs at h with hd
  · refine ⟨hd.1, hd.2, ?_⟩
    rw [roughVar_apply] at h
    split_ifs at h with hr
    · exact hr
    · exact absurd rfl h
  · exact absurd rfl h

/-- Generic convolution bound: if every factor is bounded by `B_i` on `[0, M]`, then
`|(∏ f_i)(m)| ≤ (∏ B_i) d_{|s|}(m)` for `m ≤ M`. -/
theorem abs_prod_apply_le {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ)
    (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i) (M : ℕ) (hf : ∀ i ∈ s, ∀ a ≤ M, |f i a| ≤ B i) :
    ∀ m ≤ M, |(∏ i ∈ s, f i) m| ≤ (∏ i ∈ s, B i) *
      (((ζ : ArithmeticFunction ℝ)) ^ s.card) m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m _
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul]
    rw [one_apply]; split_ifs <;> simp
  | insert a s ha ih =>
    intro m hm
    have hBs : ∀ i ∈ s, 0 ≤ B i := fun i hi => hB i (mem_insert_of_mem hi)
    have hfs : ∀ i ∈ s, ∀ a ≤ M, |f i a| ≤ B i := fun i hi => hf i (mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ',
      mul_apply, coe_zeta_mul_apply, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Nat.sum_divisorsAntidiagonal' (fun x y => |f a x * (∏ i ∈ s, f i) y|)]
    refine Finset.sum_le_sum (fun d hd => ?_)
    obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.1 hd
    have hd1 : m / d ≤ M := (Nat.div_le_self _ _).trans hm
    have hd2 : d ≤ M := (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm).trans hm
    rw [abs_mul]
    have h1 := hf a (mem_insert_self a s) (m / d) hd1
    have h2 := ih hBs hfs d hd2
    calc |f a (m / d)| * |(∏ i ∈ s, f i) d|
        ≤ B a * ((∏ i ∈ s, B i) * (((ζ : ArithmeticFunction ℝ)) ^ s.card) d) :=
          mul_le_mul h1 h2 (abs_nonneg _) (hB a (mem_insert_self a s))
      _ = B a * (∏ i ∈ s, B i) * (((ζ : ArithmeticFunction ℝ)) ^ s.card) d := by ring

/-- `d_k(m) = (ζ^k)(m) ≥ 0`. -/
theorem zetaPow_nonneg (k m : ℕ) : 0 ≤ (((ζ : ArithmeticFunction ℝ)) ^ k) m := by
  induction k generalizing m with
  | zero => rw [pow_zero, one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', coe_zeta_mul_apply]
    exact Finset.sum_nonneg (fun d _ => ih d)

/-- **Divisor bound** `d_k(m) ≤ τ(m)^{k-1}` (`k ≥ 1`, `m ≥ 1`). -/
theorem divisorPow_le (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    (((ζ : ArithmeticFunction ℝ)) ^ (k + 1)) m ≤ (m.divisors.card : ℝ) ^ k := by
  induction k generalizing m with
  | zero =>
    rw [zero_add, pow_one, natCoe_apply, zeta_apply, if_neg hm]; simp
  | succ k ih =>
    rw [pow_succ' _ (k + 1), coe_zeta_mul_apply]
    calc ∑ d ∈ m.divisors, (((ζ : ArithmeticFunction ℝ)) ^ (k + 1)) d
        ≤ ∑ d ∈ m.divisors, (m.divisors.card : ℝ) ^ k := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          obtain ⟨hdm, -⟩ := Nat.mem_divisors.1 hd
          have hd0 : d ≠ 0 := fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ hdm))
          refine (ih hd0).trans ?_
          apply pow_le_pow_left₀ (Nat.cast_nonneg _)
          exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm hdm)
      _ = (m.divisors.card : ℝ) ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, pow_succ]; ring

/-- **Coefficient bound for `β`**: `|β_m| ≤ (1 + log m)^5 d_5(m)`, with `d_5(m) ≤ τ(m)^4`. -/
theorem abs_betaSeq_le (z z₀ j : ℕ) (e : Fin 6 → ℕ) (c : Fin 6) {m : ℕ} :
    |betaSeq z z₀ j e c m| ≤ (1 + Real.log m) ^ 5 *
      (((ζ : ArithmeticFunction ℝ)) ^ 5) m := by
  have hcard : (univ.erase c).card = 5 := by rw [Finset.card_erase_of_mem (mem_univ c)]; simp
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have h := abs_prod_apply_le (univ.erase c) (fun i => dy (e i) (roughVar z₀ (hbVar z j i)))
    (fun _ => 1 + Real.log m) (fun _ _ => by linarith) m (fun i _ a ha => by
      have h0 : 0 ≤ 1 + Real.log a := by linarith [Real.log_natCast_nonneg a]
      refine (abs_dy_le h0 (abs_roughVar_le h0 (abs_hbVar_le z j i a))).trans ?_
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · simp [hlogm]
      · have : Real.log a ≤ Real.log m :=
          Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast ha)
        linarith) m le_rfl
  rw [Finset.prod_const, hcard] at h
  unfold betaSeq
  exact h

end Erdos287.Physical.TypeII
