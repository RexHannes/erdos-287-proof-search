import RequestProject.Erdos287.W2984Publication.Providers

/-!
# W2.984 — the exact implication `S₁, S₂, S₃, square-tail providers ⟹ W2.984`

**ERDŐS #287 REMAINS OPEN.  This file is kernel-checked; its only inputs are the explicit,
never-constructed providers of `Providers.lean`.  W2.984 is CONDITIONAL, asymptotic and
INEFFECTIVE (`ineffectiveExistential`): the onset `M_s` is an existential produced by the
providers (Siegel–Walfisz / Siegel-zero dependence in the analytic inputs).**

1. `pairExpect_eq_chenS` — under the framework agreement, the W3 pair expectation **is** the
   affine Chen sum `S` with the spectator weight.
2. `pairExpect_le_chen` — the repaired Chen decomposition + the four provider bounds + the scalar
   certificate give `𝔼[1_P 1_P] ≤ (c_cert + (C₁ + C₂/2 + C₃/2) δ + (5/2)ε) 𝔐`.
3. `pairBound_of_chen` — **construction** of `PairBoundProvider P c_cert` from the four Chen
   providers (`c_cert = 796682507263/200000000000`).
4. `E_Qcount_eq`, `E_Qcount_le` — the W3 same-block pair moment is `½ ∑_b ∑_{i ≠ i'} 𝔼[1_P 1_P]`,
   hence `𝔼Q ≤ c (1+η) μ²/(2r)`.
5. `width_of_pairBound` — **generic width theorem**: a per-pair constant `c₀ ∈ [2, 8)` gives the
   width statement for every `s > c₀ - 1` (choice `c₀ < r/m < s+1`, explicit `δ`, `ε`, `η₀`,
   `μ₀ = m r/(r - m C_max)`, then the imported W3 consumer `WindowMomentData.false`).
6. **`W2984`** — `S₁ → S₂ → S₃ → square tail → ∀ s > 2.984, W3Statement s`.
7. `W2984_counterexample_form` — the publication form: `∀ s > 2.984, ∃ M_s, ∀` #287
   counterexamples `A` with `max A ≥ M_s`, `max A / min A < s`.
8. `W3_of_selbergPairBound` — the same machinery with `c₀ = 4` (BFM Lemma 4.6(iii)) recovers W3:
   the refactored framework is the W3 framework.
-/

open scoped BigOperators
open Classical Finset

namespace Erdos287.W2984Publication

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R

variable {r m K : ℕ} [NeZero r]

/-! ### 1. Pair expectation = affine Chen sum `S` -/

theorem pairExpect_eq_chenS {C : AffineContactCompiler r m K} {H a M : ℕ}
    (D : FrameworkWindowData C H a M) (b : ZMod r) {i i' : Fin K} (hii : i ≠ i') :
    pairExpect D.F C b i i' =
      chenS D.F.T (D.ν b i i') (FrameworkWindowData.Lform (C := C) b i)
        (FrameworkWindowData.Lform (C := C) b i') := by
  unfold pairExpect FiniteWeights.E chenS FrameworkWindowData.Lform
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h1 : (C.slope b i * t + 1).Prime
  · by_cases h2 : (C.slope b i' * t + 1).Prime
    · rw [D.ν_agree b i i' hii t ht h1 h2]; ring
    · simp [ind, h2]
  · simp [ind, h1]

/-! ### 2. The per-pair Chen bound -/

theorem pairExpect_le_chen {C : AffineContactCompiler r m K} {H a M : ℕ}
    (D : FrameworkWindowData C H a M) (b : ZMod r) {i i' : Fin K} (hii : i ≠ i')
    {δ ε C₁ C₂ C₃ : ℝ}
    (h1 : D.S1 b i i' ≤ (Omega1 (1/7) + C₁ * δ + ε) * D.pairNorm)
    (h2 : (2 * Omega2 (1/7) (3/14) - C₂ * δ - ε) * D.pairNorm ≤ D.S2 b i i')
    (h3 : D.S3 b i i' ≤ (2 * Omega3 (1/7) (3/14) + C₃ * δ + ε) * D.pairNorm)
    (hsq : D.Ssq b i i' ≤ ε * D.pairNorm) :
    pairExpect D.F C b i i' ≤
      (chenCertificate + (C₁ + C₂ / 2 + C₃ / 2) * δ + 5 / 2 * ε) * D.pairNorm := by
  rw [pairExpect_eq_chenS D b hii]
  have hchen := chen_weighted D.sift (chenY D.X) (chenZ D.X) D.F.T (D.ν b i i')
    (FrameworkWindowData.Lform (C := C) b i) (FrameworkWindowData.Lform (C := C) b i')
    D.sift_prime (chenY_le_chenZ D.X_ge_one) (fun t _ => D.ν_nonneg b i i' t)
    (fun t ht _ => D.formsBig t ht b i')
  have hcert := mul_le_mul_of_nonneg_right pairConstant_le_certificate D.pairNorm_pos.le
  unfold pairConstant at hcert
  unfold FrameworkWindowData.S1 FrameworkWindowData.S2 FrameworkWindowData.S3
    FrameworkWindowData.Ssq at *
  nlinarith

variable (P : W3FrameworkProvider)

/-! ### 3. Construction of the per-pair provider from the Chen providers -/

/-- **The Chen providers yield the per-pair bound with the certified constant.** -/
noncomputable def pairBound_of_chen (S1 : AffineChenS1Provider P) (S2 : AffineChenS2Provider P)
    (S3 : AffineChenS3Provider P) (Ssq : AffineChenSquareTailProvider P) :
    PairBoundProvider P chenCertificate where
  Cerr := S1.C₁ + S2.C₂ / 2 + S3.C₃ / 2
  Cerr_nonneg := by
    have := S1.C₁_nonneg; have := S2.C₂_nonneg; have := S3.C₃_nonneg; positivity
  bound := by
    intro I hI ε hε
    obtain ⟨N₁, hN₁⟩ := S1.bound I hI (2 * ε / 5) (by positivity)
    obtain ⟨N₂, hN₂⟩ := S2.bound I hI (2 * ε / 5) (by positivity)
    obtain ⟨N₃, hN₃⟩ := S3.bound I hI (2 * ε / 5) (by positivity)
    obtain ⟨N₄, hN₄⟩ := Ssq.bound I hI (2 * ε / 5) (by positivity)
    refine ⟨max (max N₁ N₂) (max N₃ N₄), fun a M hw hM b i i' hii => ?_⟩
    have hM1 : N₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
    have hM2 : N₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
    have hM3 : N₃ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    have hM4 : N₄ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
    have := pairExpect_le_chen ((P.family I hI).data a M hw) b hii
      (hN₁ a M hw hM1 b i i' hii) (hN₂ a M hw hM2 b i i' hii) (hN₃ a M hw hM3 b i i' hii)
      (hN₄ a M hw hM4 b i i' hii)
    calc _ ≤ _ := this
      _ = _ := by ring

/-! ### 4. The W3 same-block pair moment -/

theorem choose_two_real (n : ℕ) : ((n.choose 2 : ℕ) : ℝ) = (n * n - n : ℝ) / 2 := by
  rw [Nat.choose_two_right]
  have h2 : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  rw [Nat.cast_div h2 (by norm_num)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · push_cast [Nat.cast_sub hn]; ring

theorem offDiag_card_eq_sum {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (S.offDiag.card : ℝ) =
      ∑ x ∈ (univ : Finset α).offDiag, ind (x.1 ∈ S) * ind (x.2 ∈ S) := by
  have : S.offDiag = (univ : Finset α).offDiag.filter (fun x => x.1 ∈ S ∧ x.2 ∈ S) := by
    ext x; simp [mem_offDiag]; tauto
  rw [this, card_filter]
  push_cast
  apply sum_congr rfl
  intro x _
  unfold ind
  split_ifs <;> simp_all

theorem Qcount_eq (C : AffineContactCompiler r m K) (t : ℕ) :
    (Qcount (blockCount C) t : ℝ) = 1 / 2 * ∑ b : ZMod r, ∑ x ∈ (univ : Finset (Fin K)).offDiag,
      ind (C.slope b x.1 * t + 1).Prime * ind (C.slope b x.2 * t + 1).Prime := by
  unfold Qcount
  push_cast
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro b _
  rw [choose_two_real]
  set S := (univ : Finset (Fin K)).filter (fun i => (C.slope b i * t + 1).Prime) with hS
  have hc : (blockCount C t b) = S.card := rfl
  rw [hc]
  have h := offDiag_card_eq_sum S
  rw [offDiag_card] at h
  have hsub : S.card ≤ S.card * S.card := Nat.le_mul_self _
  push_cast [Nat.cast_sub hsub] at h
  rw [h, show ∀ z : ℝ, z / 2 = 1 / 2 * z from fun z => by ring]
  congr 1
  apply sum_congr rfl
  intro x _
  simp [hS]

theorem E_Qcount_eq (F : FiniteWeights) (C : AffineContactCompiler r m K) :
    F.E (fun t => (Qcount (blockCount C) t : ℝ)) =
      1 / 2 * ∑ b : ZMod r, ∑ x ∈ (univ : Finset (Fin K)).offDiag, pairExpect F C b x.1 x.2 := by
  unfold FiniteWeights.E pairExpect FiniteWeights.E
  simp_rw [Qcount_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro t _
  ring

theorem E_Qcount_le (F : FiniteWeights) (C : AffineContactCompiler r m K) {c μ η 𝔐 : ℝ}
    (hc : 0 ≤ c) (h𝔐 : 0 < 𝔐) (hnorm : 𝔐 * ((r : ℝ) * K) ^ 2 ≤ (1 + η) * μ ^ 2)
    (hpair : ∀ b i i', i ≠ i' → pairExpect F C b i i' ≤ c * 𝔐) :
    F.E (fun t => (Qcount (blockCount C) t : ℝ)) ≤ c * (1 + η) * μ ^ 2 / (2 * r) := by
  rw [E_Qcount_eq]
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (NeZero.pos r)
  have hsum : ∑ b : ZMod r, ∑ x ∈ (univ : Finset (Fin K)).offDiag, pairExpect F C b x.1 x.2 ≤
      ∑ _b : ZMod r, ∑ _x ∈ (univ : Finset (Fin K)).offDiag, c * 𝔐 := by
    apply sum_le_sum; intro b _; apply sum_le_sum; intro x hx
    exact hpair b x.1 x.2 (mem_offDiag.1 hx).2.2
  simp only [sum_const, card_univ, ZMod.card, offDiag_card, Fintype.card_fin, nsmul_eq_mul]
    at hsum
  have hKK : ((K * K - K : ℕ) : ℝ) ≤ (K : ℝ) * K := by
    have : K ≤ K * K := Nat.le_mul_self _
    push_cast [Nat.cast_sub this]; nlinarith [show (0:ℝ) ≤ K by positivity]
  have hc𝔐 : 0 ≤ c * 𝔐 := mul_nonneg hc h𝔐.le
  have h1 : (r : ℝ) * (((K * K - K : ℕ) : ℝ) * (c * 𝔐)) ≤ (r : ℝ) * ((K : ℝ) * K * (c * 𝔐)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKK hc𝔐) hr.le
  have h2 : (r : ℝ) * ((K : ℝ) * K * (c * 𝔐)) = c * (𝔐 * ((r : ℝ) * K) ^ 2) / r := by
    field_simp
  have h3 : c * (𝔐 * ((r : ℝ) * K) ^ 2) / r ≤ c * ((1 + η) * μ ^ 2) / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hc) hr.le
  have : c * ((1 + η) * μ ^ 2) / r / 2 = c * (1 + η) * μ ^ 2 / (2 * r) := by
    field_simp
  linarith

/-! ### 5. Generic width theorem -/

/-- Choice of the block geometry: `c₀ < r/m ≤ c₀ + 1/n < s + 1`. -/
theorem exists_ratio {c₀ s : ℝ} (hc₀ : 2 ≤ c₀) (hs : c₀ - 1 < s) :
    ∃ r m : ℕ, 0 < r ∧ 1 ≤ m ∧ 2 * m ≤ r ∧ c₀ < (r : ℝ) / m ∧ ((r : ℝ) - m) / m < s := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (s + 1 - c₀))
  have hpos : 0 < s + 1 - c₀ := by linarith
  have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  set r := ⌊c₀ * n⌋₊ + 1 with hr
  have hlt : c₀ * n < r := by rw [hr]; push_cast; exact Nat.lt_floor_add_one _
  have hle : (r : ℝ) ≤ c₀ * n + 1 := by
    rw [hr]; push_cast; linarith [Nat.floor_le (show 0 ≤ c₀ * n by positivity)]
  refine ⟨r, n, by omega, hn1, ?_, ?_, ?_⟩
  · have : (2 * n : ℝ) < r := by nlinarith
    exact_mod_cast this.le
  · rw [lt_div_iff₀ hn0]; linarith
  · rw [div_lt_iff₀ hn0]
    have h1 : 1 / (s + 1 - c₀) * (s + 1 - c₀) = 1 := by field_simp
    have : 1 < n * (s + 1 - c₀) := by nlinarith
    nlinarith

/-- **Generic width theorem.**  A per-pair constant `c₀ ∈ [2, 8)` yields the width statement for
every `s > c₀ - 1`. -/
theorem width_of_pairBound {c₀ : ℝ} (hc₀ : 2 ≤ c₀) (hc₈ : c₀ < 8) (PB : PairBoundProvider P c₀) :
    ∀ s : ℝ, c₀ - 1 < s → W3Statement s := by
  -- reduce to `s ≤ 7`
  suffices key : ∀ s : ℝ, c₀ - 1 < s → s ≤ 7 → W3Statement s by
    intro s hs
    rcases le_total s 7 with h7 | h7
    · exact key s hs h7
    · exact (key 7 (by linarith) le_rfl).mono h7
  intro s hs hs7
  obtain ⟨r, m, hr0, hm, hr, hρ, hwidth⟩ := exists_ratio hc₀ hs
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  set ρ : ℝ := (r : ℝ) / m with hρdef
  set room : ℝ := ρ - c₀ with hroom
  have hroom0 : 0 < room := by rw [hroom]; linarith
  have hρpos : 0 < ρ := by linarith
  set δ : ℝ := min P.δmax (room / (8 * (PB.Cerr + 1))) with hδdef
  have hCe := PB.Cerr_nonneg
  have hδ0 : 0 < δ := lt_min P.δmax_pos (by positivity)
  have hδle : δ ≤ P.δmax := min_le_left _ _
  have hCδ : PB.Cerr * δ ≤ room / 8 := by
    have h1 : δ ≤ room / (8 * (PB.Cerr + 1)) := min_le_right _ _
    have h2 : PB.Cerr * δ ≤ PB.Cerr * (room / (8 * (PB.Cerr + 1))) :=
      mul_le_mul_of_nonneg_left h1 hCe
    have h3 : PB.Cerr * (room / (8 * (PB.Cerr + 1))) ≤ room / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  set ε : ℝ := room / 8 with hεdef
  have hε0 : 0 < ε := by positivity
  set η₀ : ℝ := room / (4 * ρ) with hη₀def
  have hη₀ : 0 < η₀ := by positivity
  set Cmax : ℝ := (c₀ + room / 4) * (1 + η₀) with hCmax
  have hCmax_lt : Cmax < ρ := by
    have h1 : (c₀ + room / 4) * η₀ < room / 4 := by
      rw [hη₀def, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
      have : c₀ + room / 4 < ρ := by linarith
      nlinarith
    rw [hCmax]; nlinarith
  have hCmax_lt' : (m : ℝ) * Cmax < r := by
    have := mul_lt_mul_of_pos_left hCmax_lt hm0
    rwa [hρdef, mul_div_cancel₀ _ hm0.ne'] at this
  set μ₀ : ℝ := (m : ℝ) * r / (r - m * Cmax) with hμ₀
  haveI : NeZero r := ⟨hr0.ne'⟩
  let I : FamilyIndex := ⟨r, m, hr0, hm, hr, s, hwidth, hs7, δ, hδ0, μ₀, η₀, hη₀⟩
  haveI : NeZero I.r := ⟨hr0.ne'⟩
  set Fam := P.family I hδle with hFam
  obtain ⟨N₀, hN₀⟩ := PB.bound I hδle ε hε0
  refine ⟨max Fam.onset N₀, fun W ha hM hsM => ?_⟩
  have hw : WideWindow s Fam.onset W.a W.M :=
    W3Publication.wide_of_exactWord W ha (le_trans (le_max_left _ _) hM) hsM
  set D := Fam.data W.a W.M hw with hD
  set c' : ℝ := c₀ + PB.Cerr * δ + ε with hc'
  have hc'0 : 0 ≤ c' := by rw [hc']; have := mul_nonneg hCe hδ0.le; linarith
  have hc'le : c' ≤ c₀ + room / 4 := by rw [hc']; linarith
  have hpair : ∀ b i i', i ≠ i' → pairExpect D.F Fam.compiler b i i' ≤ c' * D.pairNorm :=
    fun b i i' hii => hN₀ W.a W.M hw (le_trans (le_max_right _ _) hM) b i i' hii
  have hQ := E_Qcount_le D.F Fam.compiler hc'0 D.pairNorm_pos D.normalizer hpair
  have hη := Fam.η_small W.a W.M hw
  have hηn := D.η_nonneg
  set Cpair : ℝ := c' * (1 + D.η) with hCpair
  have hCpair_le : Cpair ≤ Cmax := by
    rw [hCpair, hCmax]
    exact mul_le_mul hc'le (by simpa using hη) (by linarith) (by linarith)
  have hCpair_lt : Cpair < (r : ℝ) / m := lt_of_le_of_lt hCpair_le hCmax_lt
  have hμ := Fam.μ_large W.a W.M hw
  have hμbig : (m : ℝ) * r / (r - m * Cpair) < D.μ := by
    have hden1 : 0 < (r : ℝ) - m * Cmax := by linarith
    have hden2 : (r : ℝ) - m * Cmax ≤ r - m * Cpair := by
      have := mul_le_mul_of_nonneg_left hCpair_le hm0.le; linarith
    have : (m : ℝ) * r / (r - m * Cpair) ≤ μ₀ := by
      rw [hμ₀]
      exact div_le_div_of_nonneg_left (by positivity) hden1 hden2
    exact lt_of_le_of_lt this hμ
  let WD : WindowMomentData Fam.compiler Fam.H W.a W.M :=
    { F := D.F
      μ := D.μ
      Cpair := Cpair
      hμ := D.hμ
      firstMoment := D.firstMoment
      pairMoment := by rw [hCpair]; exact hQ
      pairConstant := hCpair_lt
      firstMomentLarge := hμbig
      scaleControl := D.scaleControl }
  exact WD.false hm hr

/-! ### 6–8. W2.984, its publication form, and W3 recovered -/

theorem chenCertificate_bounds : 2 ≤ chenCertificate ∧ chenCertificate < 8 ∧
    chenCertificate - 1 < 2.984 := by
  unfold chenCertificate; norm_num

/-- **W2.984 (CONDITIONAL on the four Chen providers and the W3 framework; asymptotic;
ineffective).**  For every `s > 2.984` there is `M_s` such that no exact #287 word with
`M ≥ M_s` has `s · a ≤ M`. -/
theorem W2984 (S1 : AffineChenS1Provider P) (S2 : AffineChenS2Provider P)
    (S3 : AffineChenS3Provider P) (Ssq : AffineChenSquareTailProvider P) :
    ∀ s : ℝ, 2.984 < s → W3Statement s := by
  obtain ⟨h2, h8, h1⟩ := chenCertificate_bounds
  intro s hs
  exact width_of_pairBound P h2 h8 (pairBound_of_chen P S1 S2 S3 Ssq) s (by linarith)

/-- **W2.984, publication form.** -/
theorem W2984_counterexample_form (S1 : AffineChenS1Provider P) (S2 : AffineChenS2Provider P)
    (S3 : AffineChenS3Provider P) (Ssq : AffineChenSquareTailProvider P) :
    ∀ s : ℝ, 2.984 < s → ∃ Ms : ℕ, ∀ A : Finset ℕ, ∀ hA : Erdos287Counterexample A,
      Ms ≤ A.max' hA.nonempty → (A.max' hA.nonempty : ℝ) / A.min' hA.nonempty < s := by
  intro s hs
  obtain ⟨Ms, hMs⟩ := W3Publication.counterexample_form (W2984 P S1 S2 S3 Ssq s hs)
  refine ⟨Ms, fun A hA hM => ?_⟩
  have ha := ofCounterexample_one_lt_a hA
  have hapos : (0 : ℝ) < A.min' hA.nonempty := by
    have : (0 : ℝ) < (ofCounterexample hA).a := by
      have : 0 < (ofCounterexample hA).a := by omega
      exact_mod_cast this
    rwa [ofCounterexample_a] at this
  rw [div_lt_iff₀ hapos]
  by_contra hcon
  push_neg at hcon
  exact hMs A hA hM (by linarith)

/-- **W3 recovered** from the same framework with the Selberg constant `4`
(BFM Lemma 4.6(iii)). -/
theorem W3_of_selbergPairBound (PB : PairBoundProvider P 4) :
    ∀ s : ℝ, 3 < s → W3Statement s := by
  intro s hs
  exact width_of_pairBound P (by norm_num) (by norm_num) PB s (by linarith)

end Erdos287.W2984Publication
