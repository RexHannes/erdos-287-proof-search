import RequestProject.Erdos287.PostV71V87.Model

/-!
# Erdős #287 — V87 reciprocal subset-sum image: definitions and the block decomposition

`S_rec(H) = |{ ∑_{j ∈ J} 1/j : J ⊆ [1, H] }|`.

Unconditional (elementary) results:

* `recipImage_card_le_two_pow` — `|Img(X)| ≤ 2^|X|`;
* `recipImage_union_card_le`  — `|Img(X ∪ Y)| ≤ |Img X| · |Img Y|` (sumset bound);
* `smoothPart`, `roughPart`  — the `y`-smooth / large-prime block decomposition of `[1,H]`;
* `roughPart_card_le`        — `|rough| ≤ ∑_{y < p ≤ H} ⌊H/p⌋` (large-prime blocks);
* `smoothImage_card_le`      — `|Img(smooth)| ≤ H · H^{π(y)} + 1`;
* `Srec_block_bound`         — **block decomposition bound**
  `S_rec(H) ≤ (H·H^{π(y)} + 1) · 2^{∑_{y<p≤H} ⌊H/p⌋}`;
* `recip_sum_num_le`         — the reduced numerator of any element of `Img([1,H])` is at
  most `H · H!`.
-/

open scoped BigOperators

namespace Erdos287.PostV71V87

/-- The reciprocal subset-sum image of a finite set `X`. -/
def recipImage (X : Finset ℕ) : Finset ℚ :=
  X.powerset.image (fun J : Finset ℕ => ∑ j ∈ J, (1 : ℚ) / (j : ℚ))

/-- `S_rec(H) = |Img([1, H])|`. -/
def Srec (H : ℕ) : ℕ := (recipImage (Finset.Icc 1 H)).card

theorem mem_recipImage {X : Finset ℕ} {σ : ℚ} :
    σ ∈ recipImage X ↔ ∃ J ⊆ X, ∑ j ∈ J, (1 : ℚ) / j = σ := by
  simp [recipImage]

theorem recipImage_card_le_two_pow (X : Finset ℕ) : (recipImage X).card ≤ 2 ^ X.card := by
  unfold recipImage
  exact le_trans Finset.card_image_le (by rw [Finset.card_powerset])

theorem Srec_pos (H : ℕ) : 0 < Srec H :=
  Finset.card_pos.2 ⟨0, mem_recipImage.2 ⟨∅, Finset.empty_subset _, by simp⟩⟩

/-- Sumset bound for the reciprocal image of a union. -/
theorem recipImage_union_card_le (X Y : Finset ℕ) :
    (recipImage (X ∪ Y)).card ≤ (recipImage X).card * (recipImage Y).card := by
  classical
  have hsub : recipImage (X ∪ Y) ⊆ Finset.image₂ (· + ·) (recipImage X) (recipImage Y) := by
    intro σ hσ
    obtain ⟨J, hJ, rfl⟩ := mem_recipImage.1 hσ
    refine Finset.mem_image₂.2 ⟨∑ j ∈ J ∩ X, (1 : ℚ) / j,
      mem_recipImage.2 ⟨J ∩ X, Finset.inter_subset_right, rfl⟩,
      ∑ j ∈ J \ X, (1 : ℚ) / j, mem_recipImage.2 ⟨J \ X, ?_, rfl⟩,
      Finset.sum_inter_add_sum_diff _ _ _⟩
    intro j hj
    simp only [Finset.mem_sdiff] at hj
    rcases Finset.mem_union.1 (hJ hj.1) with h | h
    · exact absurd h hj.2
    · exact h
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image₂_le _ _ _)

theorem recipImage_mono {X Y : Finset ℕ} (h : X ⊆ Y) : recipImage X ⊆ recipImage Y := by
  intro σ hσ
  obtain ⟨J, hJ, rfl⟩ := mem_recipImage.1 hσ
  exact mem_recipImage.2 ⟨J, hJ.trans h, rfl⟩

/-! ## Smooth / large-prime decomposition -/

/-- The `y`-smooth part of `[1, H]`. -/
def smoothPart (y H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter (fun n => ∀ p ∈ n.primeFactors, p ≤ y)

/-- The rough part: elements of `[1,H]` with a prime factor `> y`. -/
def roughPart (y H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter (fun n => ¬ ∀ p ∈ n.primeFactors, p ≤ y)

/-- The large primes `y < p ≤ H`. -/
def largePrimes (y H : ℕ) : Finset ℕ := (Finset.Ioc y H).filter Nat.Prime

/-- The large-prime block sum `∑_{y < p ≤ H} ⌊H/p⌋`. -/
def blockSum (y H : ℕ) : ℕ := ∑ p ∈ largePrimes y H, H / p

theorem Icc_eq_smooth_union_rough (y H : ℕ) :
    Finset.Icc 1 H = smoothPart y H ∪ roughPart y H := by
  unfold smoothPart roughPart
  rw [Finset.filter_union_filter_not_eq]

/-- Multiples of `p` in `[1, H]` number `⌊H/p⌋`. -/
theorem card_multiples_Icc (H p : ℕ) : ((Finset.Icc 1 H).filter (fun n => p ∣ n)).card = H / p := by
  have : Finset.Icc 1 H = Finset.Ioc 0 H := by ext n; simp; omega
  rw [this]; exact Nat.Ioc_filter_dvd_card_eq_div H p

/-- **Large-prime blocks.**  `|rough part| ≤ ∑_{y<p≤H} ⌊H/p⌋`. -/
theorem roughPart_card_le (y H : ℕ) : (roughPart y H).card ≤ blockSum y H := by
  classical
  have hsub : roughPart y H ⊆
      (largePrimes y H).biUnion (fun p => (Finset.Icc 1 H).filter (fun n => p ∣ n)) := by
    intro n hn
    simp only [roughPart, Finset.mem_filter, not_forall, not_le] at hn
    obtain ⟨hnI, p, hp, hpy⟩ := hn
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hn1 := Finset.mem_Icc.1 hnI
    refine Finset.mem_biUnion.2 ⟨p, ?_, Finset.mem_filter.2 ⟨hnI, hpd⟩⟩
    simp only [largePrimes, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hpy, le_trans (Nat.le_of_dvd (by omega) hpd) hn1.2⟩, hpp⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  unfold blockSum
  exact le_of_eq (Finset.sum_congr rfl (fun p _ => card_multiples_Icc H p))

/-- The smooth modulus `P_y(H) = ∏_{p ≤ y} p^{⌊log_p H⌋}`. -/
def smoothModulus (y H : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow (y + 1), p ^ Nat.log p H

theorem smoothModulus_pos (y H : ℕ) : 0 < smoothModulus y H :=
  Finset.prod_pos (fun _ hp => pow_pos (Nat.prime_of_mem_primesBelow hp).pos _)

/-- `P_y(H) ≤ H^{π(y)}` for `H ≥ 1`. -/
theorem smoothModulus_le (y H : ℕ) (hH : 1 ≤ H) :
    smoothModulus y H ≤ H ^ Nat.primeCounting y := by
  unfold smoothModulus
  have hc : (Nat.primesBelow (y + 1)).card = Nat.primeCounting y := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  rw [← hc]
  exact Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_log_le_self p (by omega))

/-- Every `y`-smooth `n ≤ H` divides `P_y(H)`. -/
theorem dvd_smoothModulus {y H n : ℕ} (hn : n ∈ smoothPart y H) : n ∣ smoothModulus y H := by
  simp only [smoothPart, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnH⟩, hsm⟩ := hn
  have hn0 : n ≠ 0 := by omega
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  unfold smoothModulus
  have hsub : n.primeFactors ⊆ Nat.primesBelow (y + 1) := by
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨by have := hsm p hp; omega, Nat.prime_of_mem_primeFactors hp⟩
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => ?_))
    (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  have hp := Nat.prime_of_mem_primeFactors hp
  refine pow_dvd_pow p ?_
  have hle : p ^ n.factorization p ≤ H :=
    le_trans (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)) hnH
  exact Nat.le_log_of_pow_le hp.one_lt hle

/-- A subset sum over a set of divisors of `L` is `k / L` with `k ≤ |J| · L`. -/
theorem subset_sum_eq_div {L : ℕ} (hL : 0 < L) {J : Finset ℕ} (hJ : ∀ j ∈ J, j ∣ L)
    (hJ0 : ∀ j ∈ J, 0 < j) :
    ∑ j ∈ J, (1 : ℚ) / j = ((∑ j ∈ J, L / j : ℕ) : ℚ) / L ∧ ∑ j ∈ J, L / j ≤ J.card * L := by
  constructor
  · rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Nat.cast_div (hJ j hj) (by have := hJ0 j hj; positivity)]
    have : (j : ℚ) ≠ 0 := by have := hJ0 j hj; positivity
    have : (L : ℚ) ≠ 0 := by positivity
    field_simp
  · calc ∑ j ∈ J, L / j ≤ ∑ _j ∈ J, L := Finset.sum_le_sum (fun j _ => Nat.div_le_self _ _)
      _ = J.card * L := by simp

/-- If every element of `X ⊆ [1, H]` divides `L > 0`, then `|Img X| ≤ H · L + 1`. -/
theorem recipImage_card_le_of_dvd {X : Finset ℕ} {H L : ℕ} (hL : 0 < L)
    (hX : X ⊆ Finset.Icc 1 H) (hdvd : ∀ n ∈ X, n ∣ L) :
    (recipImage X).card ≤ H * L + 1 := by
  have hsub : recipImage X ⊆ (Finset.range (H * L + 1)).image (fun k : ℕ => (k : ℚ) / L) := by
    intro σ hσ
    obtain ⟨J, hJ, rfl⟩ := mem_recipImage.1 hσ
    have hJ0 : ∀ j ∈ J, 0 < j := fun j hj => by have := Finset.mem_Icc.1 (hX (hJ hj)); omega
    obtain ⟨h1, h2⟩ := subset_sum_eq_div hL (fun j hj => hdvd j (hJ hj)) hJ0
    refine Finset.mem_image.2 ⟨∑ j ∈ J, L / j, Finset.mem_range.2 ?_, h1.symm⟩
    have hcard : J.card ≤ H := by
      have := Finset.card_le_card (hJ.trans hX); simp at this; omega
    have := Nat.mul_le_mul_right L hcard
    omega
  exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))

/-- **Smooth image bound.**  `|Img(smooth part)| ≤ H · P_y(H) + 1`. -/
theorem smoothImage_card_le_modulus (y H : ℕ) :
    (recipImage (smoothPart y H)).card ≤ H * smoothModulus y H + 1 :=
  recipImage_card_le_of_dvd (smoothModulus_pos y H) (Finset.filter_subset _ _)
    (fun _ hn => dvd_smoothModulus hn)

/-- `|Img(smooth part)| ≤ H · H^{π(y)} + 1`. -/
theorem smoothImage_card_le (y H : ℕ) (hH : 1 ≤ H) :
    (recipImage (smoothPart y H)).card ≤ H * H ^ Nat.primeCounting y + 1 := by
  refine le_trans (smoothImage_card_le_modulus y H) ?_
  have := smoothModulus_le y H hH
  have := Nat.mul_le_mul_left H this
  omega

/-- **Block decomposition bound.**
`S_rec(H) ≤ (H · H^{π(y)} + 1) · 2^{∑_{y<p≤H} ⌊H/p⌋}`. -/
theorem Srec_block_bound (y H : ℕ) (hH : 1 ≤ H) :
    Srec H ≤ (H * H ^ Nat.primeCounting y + 1) * 2 ^ blockSum y H := by
  unfold Srec
  rw [Icc_eq_smooth_union_rough y H]
  refine le_trans (recipImage_union_card_le _ _) (Nat.mul_le_mul (smoothImage_card_le y H hH) ?_)
  exact le_trans (recipImage_card_le_two_pow _) (Nat.pow_le_pow_right (by norm_num)
    (roughPart_card_le y H))

/-! ## Numerator bound -/

/-- The reduced numerator of a nonnegative element of `Img([1,H])` is at most `H · H!`. -/
theorem recip_sum_num_le {H : ℕ} {σ : ℚ} (hσ : σ ∈ recipImage (Finset.Icc 1 H)) :
    σ.num.natAbs ≤ H * H.factorial := by
  obtain ⟨J, hJ, rfl⟩ := mem_recipImage.1 hσ
  have hJ0 : ∀ j ∈ J, 0 < j := fun j hj => by have := Finset.mem_Icc.1 (hJ hj); omega
  have hdvd : ∀ j ∈ J, j ∣ H.factorial := fun j hj =>
    Nat.dvd_factorial (hJ0 j hj) (Finset.mem_Icc.1 (hJ hj)).2
  obtain ⟨h1, h2⟩ := subset_sum_eq_div (Nat.factorial_pos H) hdvd hJ0
  rw [h1]
  set k := ∑ j ∈ J, H.factorial / j
  have hk : k ≤ H * H.factorial := by
    have hc : J.card ≤ H := by
      have := Finset.card_le_card hJ; simp at this; omega
    exact le_trans h2 (Nat.mul_le_mul_right _ hc)
  have hnd : ((k : ℚ) / (H.factorial : ℚ)).num ∣ (k : ℤ) := by
    have := Rat.num_dvd (k : ℤ) (b := (H.factorial : ℤ))
      (by exact_mod_cast (Nat.factorial_pos H).ne')
    rw [Rat.divInt_eq_div] at this
    simpa using this
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]; simp
  · have := Int.natAbs_le_of_dvd_ne_zero hnd (by exact_mod_cast hpos.ne')
    simp at this
    omega

end Erdos287.PostV71V87
