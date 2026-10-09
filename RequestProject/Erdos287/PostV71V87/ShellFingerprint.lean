import RequestProject.Erdos287.PostV71V87.ReciprocalImage
import RequestProject.Erdos287.PostV71V87.EndpointCRT

/-!
# Erdős #287 — V87 all-base shell fingerprint and the entropy core (unconditional)

**All-base shell fingerprint** (`shell_fingerprint`).  For every prime `p < q_*` the maximal
primary layer is genuinely active (`maxVal ≥ 1`, at least two elements), and its reciprocal
cofactor sum

  `σ_p = ∑_{n ∈ layer p} 1 / (n / P_p)`

has reduced numerator divisible by `p`.

**Entropy core** (`entropy_core`).  Fix `K ≥ 1` and put `q = q_*`, `H = ⌊K M / q⌋`.  Every
prime `p` with `q < K p` and `p < q` has all cofactors in `[1, H]`, so `σ_p` is a non-zero
element of the reciprocal image `Img([1,H])` whose numerator is divisible by `p`.  Hence

  `q ^ #P ≤ K ^ #P · (H · H!) ^ {S_rec(H)}`,   `P = {p prime : p < q < K p}`.

This is the purely arithmetic input of the V87 entropy inversion; the analytic part is in
`EntropyInversion.lean`.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- If `∑ (f n)⁻¹ = 0` in `ZMod p` with every `f n` prime to `p`, then `p` divides the
reduced numerator of `∑ 1 / f n`. -/
theorem num_dvd_of_zmod_inv_sum {p : ℕ} (hp : p.Prime) (T : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ n ∈ T, ¬ p ∣ f n) (hsum : ∑ n ∈ T, ((f n : ℕ) : ZMod p)⁻¹ = 0) :
    (p : ℤ) ∣ (∑ n ∈ T, (1 : ℚ) / (f n : ℚ)).num := by
  haveI := Fact.mk hp
  have hf0 : ∀ n ∈ T, f n ≠ 0 := fun n hn h => hf n hn (h ▸ dvd_zero p)
  set L := ∏ n ∈ T, f n with hLdef
  have hLp : ¬ p ∣ L := by
    rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨n, hn, h⟩; exact hf n hn h
  have hL0 : L ≠ 0 := Finset.prod_ne_zero_iff.2 hf0
  have hdvd : ∀ n ∈ T, f n ∣ L := fun n hn => Finset.dvd_prod_of_mem f hn
  set K := ∑ n ∈ T, L / f n with hKdef
  -- `σ · L = K`
  have hσ : (∑ n ∈ T, (1 : ℚ) / (f n : ℚ)) * L = K := by
    rw [hKdef, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Nat.cast_div (hdvd n hn) (by exact_mod_cast hf0 n hn)]
    have : (f n : ℚ) ≠ 0 := by exact_mod_cast hf0 n hn
    field_simp
  -- `p ∣ K`
  have hK : p ∣ K := by
    rw [← ZMod.natCast_eq_zero_iff, hKdef, Nat.cast_sum]
    have : ∀ n ∈ T, ((L / f n : ℕ) : ZMod p) = (L : ZMod p) * ((f n : ℕ) : ZMod p)⁻¹ := by
      intro n hn
      have hfn : ((f n : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hf n hn
      rw [Nat.cast_div (hdvd n hn) hfn, div_eq_mul_inv]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hsum, mul_zero]
  -- transfer to the numerator
  set σ := ∑ n ∈ T, (1 : ℚ) / (f n : ℚ)
  have hnd : σ.num * (L : ℤ) = (K : ℤ) * σ.den := by
    have h1 : (σ.num : ℚ) / σ.den * L = K := by rw [Rat.num_div_den]; exact hσ
    have hd : (σ.den : ℚ) ≠ 0 := by exact_mod_cast σ.den_pos.ne'
    have h2 : (σ.num : ℚ) * L = K * σ.den := by field_simp at h1; linarith
    exact_mod_cast h2
  have h3 : (p : ℤ) ∣ σ.num * (L : ℤ) := by
    rw [hnd]; exact Dvd.dvd.mul_right (by exact_mod_cast hK) _
  rcases (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd h3 with h | h
  · exact h
  · exact absurd (by exact_mod_cast h) hLp

namespace ExactWord

variable (W : ExactWord)

/-- The cofactor of a layer element: `n / P_p`. -/
def cof (p n : ℕ) : ℕ := n / W.P p

/-- The reciprocal cofactor sum of the maximal `p`-layer. -/
def sigma (p : ℕ) : ℚ := ∑ n ∈ W.layer p, (1 : ℚ) / (W.cof p n : ℚ)

theorem cof_eq_ordCompl {p n : ℕ} (hn : n ∈ W.layer p) : W.cof p n = ordCompl[p] n := by
  unfold cof Word.P
  rw [(mem_topLayer.1 hn).2]; rfl

theorem cof_mul {p n : ℕ} (hp : p.Prime) (hn : n ∈ W.layer p) : W.P p * W.cof p n = n :=
  Nat.mul_div_cancel' (W.P_dvd_of_mem_layer hp hn)

theorem cof_pos {p n : ℕ} (hp : p.Prime) (hn : n ∈ W.layer p) : 0 < W.cof p n := by
  have h1 := W.cof_mul hp hn
  have h2 := W.pos_of_mem (W.mem_of_mem_layer hn)
  refine Nat.pos_of_ne_zero (fun h => ?_)
  rw [h, mul_zero] at h1; omega

theorem not_dvd_cof {p n : ℕ} (hp : p.Prime) (hn : n ∈ W.layer p) : ¬ p ∣ W.cof p n := by
  rw [W.cof_eq_ordCompl hn]
  exact Nat.not_dvd_ordCompl hp (W.pos_of_mem (W.mem_of_mem_layer hn)).ne'

/-- **Fingerprint for an active prime.**  `p` divides the reduced numerator of `σ_p`. -/
theorem prime_dvd_sigma_num {p : ℕ} (hp : p.Prime) (hact : W.Active p) :
    (p : ℤ) ∣ (W.sigma p).num := by
  refine num_dvd_of_zmod_inv_sum hp (W.layer p) (W.cof p) (fun n hn => W.not_dvd_cof hp hn) ?_
  have := topLayer_congruence W.A p hp W.pos_of_mem' W.mass hact
  rw [← this]
  exact Finset.sum_congr rfl (fun n hn => by rw [W.cof_eq_ordCompl hn])

theorem sigma_pos {p : ℕ} (hp : p.Prime) : 0 < W.sigma p := by
  unfold sigma
  exact Finset.sum_pos (fun n hn => by have := W.cof_pos hp hn; positivity) (W.layer_nonempty p)

/-- **All-base shell fingerprint.**  For every prime `p < q_*`: the row is active, the
maximal layer has at least two elements, and `p` divides the reduced numerator of the
reciprocal cofactor sum `σ_p`. -/
theorem shell_fingerprint {p : ℕ} (hp : p.Prime) (hlt : p < W.qstar) :
    W.Active p ∧ 2 ≤ (W.layer p).card ∧ (p : ℤ) ∣ (W.sigma p).num := by
  have hact := W.active_of_lt_qstar hp hlt
  exact ⟨hact, W.two_le_layer_card hp hact, W.prime_dvd_sigma_num hp hact⟩

/-- Cofactors are injective on a layer. -/
theorem cof_injOn {p : ℕ} (hp : p.Prime) : Set.InjOn (W.cof p) (W.layer p : Set ℕ) := by
  intro n hn m hm h
  have h1 := W.cof_mul hp hn
  have h2 := W.cof_mul hp hm
  rw [← h1, ← h2, h]

/-- `σ_p` is an element of the reciprocal image of `[1, H]` as soon as `M ≤ H · P_p`… more
precisely as soon as every cofactor is at most `H`. -/
theorem sigma_mem_recipImage {p H : ℕ} (hp : p.Prime)
    (hH : ∀ n ∈ W.layer p, W.cof p n ≤ H) : W.sigma p ∈ recipImage (Finset.Icc 1 H) := by
  classical
  refine mem_recipImage.2 ⟨(W.layer p).image (W.cof p), ?_, ?_⟩
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_Icc.2 ⟨W.cof_pos hp hn, hH n hn⟩
  · unfold sigma
    rw [Finset.sum_image (W.cof_injOn hp)]

/-- Cofactor bound in the top shell: if `p` is active, `q < K p`, then every cofactor is at
most `⌊K M / q⌋`. -/
theorem cof_le_shell {p K q n : ℕ} (hp : p.Prime) (hact : W.Active p) (hq0 : 0 < q)
    (hq : q < K * p) (hn : n ∈ W.layer p) : W.cof p n ≤ K * W.M / q := by
  have hpos := W.cof_pos hp hn
  have hmul := W.cof_mul hp hn
  have hPp := W.le_P_of_active hp hact
  have hnM := (W.mem_Icc (W.mem_of_mem_layer hn)).2
  have h1 : W.cof p n * p ≤ W.M := by
    calc W.cof p n * p ≤ W.cof p n * W.P p := Nat.mul_le_mul_left _ hPp
      _ = n := by rw [mul_comm]; exact hmul
      _ ≤ W.M := hnM
  rw [Nat.le_div_iff_mul_le (by omega)]
  calc W.cof p n * q ≤ W.cof p n * (K * p) := Nat.mul_le_mul_left _ hq.le
    _ = K * (W.cof p n * p) := by ring
    _ ≤ K * W.M := Nat.mul_le_mul_left _ h1

/-- The top-shell primes `{p prime : p < q_*, q_* < K p}`. -/
noncomputable def topShellPrimes (K : ℕ) : Finset ℕ :=
  (Finset.range W.qstar).filter (fun p => p.Prime ∧ W.qstar < K * p)

/-- **Entropy core (divisibility form).**  The product of the top-shell primes divides the
product of the numerators of the non-zero elements of `Img([1, ⌊K M / q_*⌋])`. -/
theorem entropy_core_dvd (K : ℕ) :
    ∏ p ∈ W.topShellPrimes K, p ∣
      ∏ σ ∈ (recipImage (Finset.Icc 1 (K * W.M / W.qstar))).filter (· ≠ 0), σ.num.natAbs := by
  refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
  · simp only [topShellPrimes, Finset.mem_filter] at hp
    exact hp.2.1.prime
  · simp only [topShellPrimes, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hlt, hpp, hK⟩ := hp
    have hact := W.active_of_lt_qstar hpp hlt
    have hmem := W.sigma_mem_recipImage hpp (fun n hn => W.cof_le_shell hpp hact (by have := W.one_lt_qstar; omega) hK hn)
    have hne : W.sigma p ≠ 0 := (W.sigma_pos hpp).ne'
    have h1 : p ∣ (W.sigma p).num.natAbs := by
      have := W.prime_dvd_sigma_num hpp hact
      exact Int.natCast_dvd.1 this
    exact dvd_trans h1 (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hmem, hne⟩))

/-- **Entropy core (size form).**
`q_*^{#P} ≤ K^{#P} · (H · H!)^{S_rec(H)}` with `H = ⌊K M / q_*⌋ ≥ 1`. -/
theorem entropy_core (K : ℕ) (hH : 1 ≤ K * W.M / W.qstar) :
    W.qstar ^ (W.topShellPrimes K).card ≤
      K ^ (W.topShellPrimes K).card *
        ((K * W.M / W.qstar) * (K * W.M / W.qstar).factorial) ^ Srec (K * W.M / W.qstar) := by
  set H := K * W.M / W.qstar
  set S := W.topShellPrimes K
  have hlow : W.qstar ^ S.card ≤ K ^ S.card * ∏ p ∈ S, p := by
    rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' (fun p hp => ?_)
    simp only [S, topShellPrimes, Finset.mem_filter] at hp
    exact hp.2.2.le
  have hN : 0 < ∏ σ ∈ (recipImage (Finset.Icc 1 H)).filter (· ≠ 0), σ.num.natAbs :=
    Finset.prod_pos (fun σ hσ => by
      simp only [Finset.mem_filter] at hσ
      exact Int.natAbs_pos.2 (Rat.num_ne_zero.2 hσ.2))
  have hmid := Nat.le_of_dvd hN (W.entropy_core_dvd K)
  have hup : ∏ σ ∈ (recipImage (Finset.Icc 1 H)).filter (· ≠ 0), σ.num.natAbs ≤
      (H * H.factorial) ^ Srec H := by
    refine le_trans (Finset.prod_le_pow_card _ _ _ (fun σ hσ =>
      recip_sum_num_le (Finset.mem_filter.1 hσ).1)) ?_
    refine Nat.pow_le_pow_right (Nat.mul_pos (by omega) (Nat.factorial_pos H)) ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  calc W.qstar ^ S.card ≤ K ^ S.card * ∏ p ∈ S, p := hlow
    _ ≤ K ^ S.card * (H * H.factorial) ^ Srec H :=
        Nat.mul_le_mul_left _ (le_trans hmid hup)

end ExactWord

end Erdos287.PostV71V87
