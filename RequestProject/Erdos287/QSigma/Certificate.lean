import RequestProject.Erdos287.QSigma.Carry

/-!
# Erdős #287 — product exclusion, the mass-sharpened product bound, and baseline transport

* `Pmax a M R k` — the largest product of an independent `F ⊆ V` with `|F| ≤ k`;
* `Pmass a M R` — the largest product of an independent `F ⊆ V` with `∑_{n∈F} 1/n ≤ τ`.

Main results:

* `prod_le_Pmass`, `Pmass_le_Pmax` — every solution has `∏ E ≤ P_mass ≤ P_max(V, R_T)`;
* `no_solution_of_QSigma_gt_Pmax` — **(CERT)** `Q_Σ > P_max(V, R_T)` kills the source;
* `no_solution_of_QSigma_gt_Pmass` — the sharper certificate `Q_Σ > P_mass`;
* `kappa_mono` — `κ_{p,d} ≤ κ_{p,d+1}` (when depth `d+1` is feasible);
* `tau_add_compulsory_mass`, `tau_transport`, `omissions_transport` — the exact
  baseline-transport law: changing the compulsory set only reclassifies omitted
  reciprocal mass; `τ_R + ∑_{r∈R} 1/r` does not depend on `R`.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

open Classical in
/-- `P_max(V, k)`: the largest product of an independent `F ⊆ V` with `|F| ≤ k`. -/
noncomputable def Pmax (a M : ℕ) (R : Finset ℕ) (k : ℕ) : ℕ :=
  (((V a M R).powerset).filter (fun F => Indep F ∧ F.card ≤ k)).sup (fun F => ∏ n ∈ F, n)

open Classical in
/-- `P_mass(V, τ)`: the largest product of an independent `F ⊆ V` with `∑_{n∈F} 1/n ≤ τ`. -/
noncomputable def Pmass (a M : ℕ) (R : Finset ℕ) : ℕ :=
  (((V a M R).powerset).filter
    (fun F => Indep F ∧ (∑ n ∈ F, (1 : ℚ) / n) ≤ tau a M R)).sup (fun F => ∏ n ∈ F, n)

/-- Every solution has product at most `P_mass`. -/
theorem prod_le_Pmass (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    (∏ n ∈ E, n) ≤ Pmass a M R := by
  classical
  unfold Pmass
  refine Finset.le_sup (f := fun F => ∏ n ∈ F, n) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h.1, h.2.1, (h.recip_eq_tau ha).le⟩

/-- Reciprocal mass bounds cardinality: an `F ⊆ V` with `∑_{n∈F} 1/n ≤ τ` has
`|F| ≤ R_T = ⌊M T / W⌋`. -/
theorem card_le_RT_of_recip_le (ha : 0 < a) {F : Finset ℕ} (hF : F ⊆ V a M R)
    (hm : (∑ n ∈ F, (1 : ℚ) / n) ≤ tau a M R) : F.card ≤ RT a M R := by
  have hW0 : W a M R ≠ 0 := W_ne_zero ha
  have hWq : (0 : ℚ) < W a M R := by exact_mod_cast Nat.pos_of_ne_zero hW0
  -- `W ≤ M · (W/n)` for each `n ∈ F`
  have hstep : ∀ n ∈ F, (W a M R : ℚ) ≤ M * ((W a M R : ℚ) * (1 / n)) := by
    intro n hn
    have hB := V_subset_B (hF hn)
    have hnpos : (0 : ℚ) < n := by exact_mod_cast pos_of_mem_B ha hB
    have hnM : (n : ℚ) ≤ M := by exact_mod_cast (mem_B.1 hB).2.1
    rw [show (M : ℚ) * ((W a M R : ℚ) * (1 / n)) = (W a M R : ℚ) * (M / n) by ring]
    have : (1 : ℚ) ≤ M / n := by rw [le_div_iff₀ hnpos]; linarith
    nlinarith
  have hsum : (F.card : ℚ) * W a M R ≤ M * T a M R := by
    have h1 : (F.card : ℚ) * W a M R ≤ ∑ n ∈ F, (M * ((W a M R : ℚ) * (1 / n))) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_le_sum (fun n hn => ?_)
      simpa using hstep n hn
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
    have h2 : (W a M R : ℚ) * ∑ n ∈ F, (1 : ℚ) / n ≤ T a M R := by
      have := mul_le_mul_of_nonneg_left hm hWq.le
      rwa [tau, mul_div_cancel₀ _ hWq.ne'] at this
    have hM0 : (0 : ℚ) ≤ M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0]
  have hT : (T a M R : ℚ) ≤ ((T a M R).toNat : ℚ) := by
    exact_mod_cast Int.self_le_toNat (T a M R)
  have hsum' : ((F.card * W a M R : ℕ) : ℚ) ≤ ((M * (T a M R).toNat : ℕ) : ℚ) := by
    push_cast
    have hM0 : (0 : ℚ) ≤ M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hT hM0]
  have : F.card * W a M R ≤ M * (T a M R).toNat := by exact_mod_cast hsum'
  rw [RT, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hW0)]
  exact this

/-- The mass-sharpened bound is never worse than the cardinality bound:
`P_mass ≤ P_max(V, R_T)`. -/
theorem Pmass_le_Pmax (ha : 0 < a) : Pmass a M R ≤ Pmax a M R (RT a M R) := by
  classical
  unfold Pmass
  refine Finset.sup_le (fun F hF => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hF
  unfold Pmax
  refine Finset.le_sup (f := fun F => ∏ n ∈ F, n) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hF.1, hF.2.1, card_le_RT_of_recip_le ha hF.1 hF.2.2⟩

/-- Every solution has product at most `P_max(V, R_T)`. -/
theorem prod_le_Pmax (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    (∏ n ∈ E, n) ≤ Pmax a M R (RT a M R) :=
  (prod_le_Pmass ha h).trans (Pmass_le_Pmax ha)

/-- `Q_Σ ≤ ∏ E` for every solution. -/
theorem QSigma_le_prod (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    QSigma a M R ≤ ∏ n ∈ E, n := by
  have hE0 : ∀ n ∈ E, n ≠ 0 := fun n hn => (pos_of_mem_B ha (V_subset_B (h.1 hn))).ne'
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 hE0))
    (QSigma_dvd_prod ha h)

/-- **(CERT, sharpened)**  `Q_Σ > P_mass(V, τ)` implies the source has no solution. -/
theorem no_solution_of_QSigma_gt_Pmass (ha : 0 < a) (hQ : Pmass a M R < QSigma a M R)
    (E : Finset ℕ) : ¬ SourceSol a M R E := fun h =>
  absurd ((QSigma_le_prod ha h).trans (prod_le_Pmass ha h)) (not_le.2 hQ)

/-- **(CERT)**  `Q_Σ > P_max(V, R_T)` implies the source has no solution. -/
theorem no_solution_of_QSigma_gt_Pmax (ha : 0 < a)
    (hQ : Pmax a M R (RT a M R) < QSigma a M R) (E : Finset ℕ) : ¬ SourceSol a M R E :=
  no_solution_of_QSigma_gt_Pmass ha (lt_of_le_of_lt (Pmass_le_Pmax ha) hQ) E

/-- **Depth monotonicity.**  If depth `d+1 ≤ e` is feasible, then `κ_{p,d} ≤ κ_{p,d+1}`. -/
theorem kappa_mono (ha : 0 < a) {p d : ℕ} (hp : p.Prime) (hd : d + 1 ≤ eW a M R p)
    (hfeas : (RepairSizes a M R p (d + 1)).Nonempty) :
    kappa a M R p d ≤ kappa a M R p (d + 1) := by
  classical
  obtain ⟨F, hFS, hFc, hFmod⟩ := Nat.sInf_mem hfeas
  set G := F.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n)
  have hG : G.card ∈ RepairSizes a M R p d := by
    refine ⟨G, ?_, rfl, ?_⟩
    · intro n hn
      rw [Finset.mem_filter] at hn
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (hFS hn.1)).1, hn.2⟩
    · have hsplit := Finset.sum_filter_add_sum_filter_not F
        (fun n => p ^ (eW a M R p - d + 1) ∣ n) (fun n => ((W a M R / n : ℕ) : ℤ))
      have hrest : ((p : ℤ) ^ d) ∣ ∑ n ∈ F.filter (fun n => ¬ p ^ (eW a M R p - d + 1) ∣ n),
          ((W a M R / n : ℕ) : ℤ) := by
        refine Finset.dvd_sum (fun n hn => ?_)
        rw [Finset.mem_filter] at hn
        have := pow_dvd_W_div_of_not_mem_S ha hp (by omega)
          (Finset.mem_filter.1 (hFS hn.1)).1 hn.2
        exact_mod_cast this
      have hmod' : (∑ n ∈ F, ((W a M R / n : ℕ) : ℤ)) ≡ T a M R [ZMOD (p : ℤ) ^ d] :=
        Int.ModEq.of_mul_right (p : ℤ) (by rw [← pow_succ]; exact hFmod)
      rw [← hsplit] at hmod'
      have h0 : ∑ n ∈ F.filter (fun n => ¬ p ^ (eW a M R p - d + 1) ∣ n),
          ((W a M R / n : ℕ) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ d] := Int.modEq_zero_iff_dvd.2 hrest
      have := (Int.ModEq.add_left (∑ n ∈ G, ((W a M R / n : ℕ) : ℤ)) h0).symm.trans hmod'
      simpa using this
  calc kappa a M R p d ≤ G.card := Nat.sInf_le hG
    _ ≤ F.card := Finset.card_filter_le _ _
    _ = kappa a M R p (d + 1) := hFc

/-! ## Baseline transport -/

/-- **Transport invariant.**  For any compulsory set `R ⊆ [a, M]`,
`τ_R + ∑_{r∈R} 1/r = ∑_{n=a}^{M} 1/n - 1`; the right side does not depend on `R`. -/
theorem tau_add_compulsory_mass (ha : 0 < a) (hR : R ⊆ Finset.Icc a M) :
    tau a M R + ∑ r ∈ R, (1 : ℚ) / r = (∑ n ∈ Finset.Icc a M, (1 : ℚ) / n) - 1 := by
  rw [tau_eq ha, B, ← Finset.sum_sdiff hR]
  ring

/-- **Exact transport law** between two baselines `R₁ ⊆ R₂ ⊆ [a, M]`:
`τ_{R₁} = τ_{R₂} + ∑_{r ∈ R₂ \ R₁} 1/r`. -/
theorem tau_transport (ha : 0 < a) {R₁ R₂ : Finset ℕ} (h12 : R₁ ⊆ R₂)
    (h2 : R₂ ⊆ Finset.Icc a M) :
    tau a M R₁ = tau a M R₂ + ∑ r ∈ R₂ \ R₁, (1 : ℚ) / r := by
  have e1 := tau_add_compulsory_mass ha (h12.trans h2)
  have e2 := tau_add_compulsory_mass ha h2
  rw [← Finset.sum_sdiff h12] at e2
  linarith

/-- **Omission transport.**  For a physical set `A ⊆ [a, M]` avoiding `R₂ ⊇ R₁`, the optional
omissions relative to `R₁` are exactly those relative to `R₂` together with `R₂ \ R₁`
(disjointly).  Changing the baseline only reclassifies the same omissions. -/
theorem omissions_transport {R₁ R₂ A : Finset ℕ} (h12 : R₁ ⊆ R₂)
    (h2 : R₂ ⊆ Finset.Icc a M) (hA : Disjoint R₂ A) :
    B a M R₁ \ A = (B a M R₂ \ A) ∪ (R₂ \ R₁) ∧ Disjoint (B a M R₂ \ A) (R₂ \ R₁) := by
  constructor
  · ext n
    simp only [B, Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨⟨hI, hR1⟩, hnA⟩
      by_cases hn2 : n ∈ R₂
      · exact Or.inr ⟨hn2, hR1⟩
      · exact Or.inl ⟨⟨hI, hn2⟩, hnA⟩
    · rintro (⟨⟨hI, hn2⟩, hnA⟩ | ⟨hn2, hR1⟩)
      · exact ⟨⟨hI, fun h => hn2 (h12 h)⟩, hnA⟩
      · exact ⟨⟨h2 hn2, hR1⟩, Finset.disjoint_left.1 hA hn2⟩
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [B, Finset.mem_sdiff] at hn hn'
    exact hn.1.2 hn'.1

end Erdos287.ExactSource
