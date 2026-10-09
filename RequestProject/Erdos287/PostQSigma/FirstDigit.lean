import RequestProject.Erdos287.PostQSigma.MandatoryLocal

/-!
# Erdős #287 — post-`Q_Σ` bank, §12 (V57): first-digit structure

**Status: BANK (proved in Lean)** for the raw source `R = ∅` with `2a ≤ M` (which follows from
`H(a,M) ≥ 1`, `harmonic_source_le_half`).  These are source theorems, not finite census claims.

Depth `d = 1`, `q = p^e` with `p^e ‖ W`.  The layer consists of the multiples `q k` of `q` in
`[a, M]`; every such `k` is prime to `p` (`not_dvd_cofactor`).

* `firstDigit_residue_ne_zero` — every first-digit residue `W/(qk) mod p` is nonzero;
* `firstDigit_pair_iff` — `W/(qk) + W/(qk') ≡ 0 (mod p) ↔ k + k' ≡ 0 (mod p)`;
* `firstDigit_mandatory_no_endpoint` — a mandatory first-digit layer contains no selected
  endpoint: `q ∤ a` and `q ∤ M`;
* `firstDigit_singleton` — a singleton mandatory first-digit layer is `{q}` or `{2q}`.

The exact classification of endpoint-free first-digit layers of size `≤ 3` (with the listed
exceptional primes) was not supplied in checkable form and is **not** formalised here.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M p : ℕ}

lemma qpd_one {a M : ℕ} {p : ℕ} (he : 1 ≤ eW a M ∅ p) : qpd a M ∅ p 1 = p ^ eW a M ∅ p := by
  unfold qpd; congr 1; omega

/-- A multiple `p^e k` of the top power lying in `B` has `p ∤ k`. -/
lemma not_dvd_cofactor (ha : 0 < a) (hp : p.Prime) {k : ℕ}
    (hB : p ^ eW a M ∅ p * k ∈ B a M ∅) : ¬ p ∣ k := by
  intro hk
  have hdvd : p ^ (eW a M ∅ p + 1) ∣ W a M ∅ := by
    rw [pow_succ]
    exact (Nat.mul_dvd_mul_left _ hk).trans (dvd_W_of_mem_B hB)
  rw [hp.pow_dvd_iff_le_factorization (W_ne_zero ha)] at hdvd
  unfold eW at hdvd; omega

/-- `p ∤ W / p^e`. -/
lemma not_dvd_W_div_top (ha : 0 < a) (hp : p.Prime) : ¬ p ∣ W a M ∅ / p ^ eW a M ∅ p :=
  Nat.not_dvd_ordCompl hp (W_ne_zero ha)

/-- `(W/(qk)) · k ≡ W/q`. -/
lemma cast_W_div_mul (ha : 0 < a) {k : ℕ} (hB : p ^ eW a M ∅ p * k ∈ B a M ∅) :
    ((W a M ∅ / (p ^ eW a M ∅ p * k) : ℕ) : ZMod p) * (k : ZMod p) =
      ((W a M ∅ / p ^ eW a M ∅ p : ℕ) : ZMod p) := by
  obtain ⟨m, hm⟩ := dvd_W_of_mem_B hB
  have hpos : 0 < p ^ eW a M ∅ p * k := pos_of_mem_B ha hB
  have hq : 0 < p ^ eW a M ∅ p := Nat.pos_of_mul_pos_right hpos
  have h1 : W a M ∅ / (p ^ eW a M ∅ p * k) = m := by
    rw [hm, Nat.mul_div_cancel_left _ hpos]
  have h2 : W a M ∅ / p ^ eW a M ∅ p = k * m := by
    rw [hm, mul_assoc, Nat.mul_div_cancel_left _ hq]
  rw [h1, h2]; push_cast; ring

/-- Every first-digit residue is nonzero mod `p`. -/
theorem firstDigit_residue_ne_zero (ha : 0 < a) (hp : p.Prime) {k : ℕ}
    (hB : p ^ eW a M ∅ p * k ∈ B a M ∅) : ¬ p ∣ W a M ∅ / (p ^ eW a M ∅ p * k) := by
  haveI := Fact.mk hp
  intro h
  have h0 : ((W a M ∅ / (p ^ eW a M ∅ p * k) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h
  have := cast_W_div_mul ha hB
  rw [h0, zero_mul, eq_comm, ZMod.natCast_eq_zero_iff] at this
  exact not_dvd_W_div_top ha hp this

/-- **Pair criterion**: `W/(qk) + W/(qk') ≡ 0 (mod p) ↔ p ∣ k + k'`. -/
theorem firstDigit_pair_iff (ha : 0 < a) (hp : p.Prime) {k k' : ℕ}
    (hB : p ^ eW a M ∅ p * k ∈ B a M ∅) (hB' : p ^ eW a M ∅ p * k' ∈ B a M ∅) :
    p ∣ W a M ∅ / (p ^ eW a M ∅ p * k) + W a M ∅ / (p ^ eW a M ∅ p * k') ↔ p ∣ k + k' := by
  haveI := Fact.mk hp
  have hk : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_cofactor ha hp hB
  have hk' : (k' : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_cofactor ha hp hB'
  have hw : ((W a M ∅ / p ^ eW a M ∅ p : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact not_dvd_W_div_top ha hp
  have e1 := cast_W_div_mul ha hB
  have e2 := cast_W_div_mul ha hB'
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  set x := ((W a M ∅ / (p ^ eW a M ∅ p * k) : ℕ) : ZMod p)
  set y := ((W a M ∅ / (p ^ eW a M ∅ p * k') : ℕ) : ZMod p)
  set w := ((W a M ∅ / p ^ eW a M ∅ p : ℕ) : ZMod p)
  have key : (x + y) * ((k : ZMod p) * k') = w * (k + k') := by
    linear_combination (k' : ZMod p) * e1 + (k : ZMod p) * e2
  constructor
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hw
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero hk hk')

/-- Divisibility form of the local criterion at depth `1` (raw source). -/
lemma sum_res_one_eq_zero_iff (F : Finset ℕ) :
    ∑ n ∈ F, res a M ∅ p 1 n = 0 ↔ p ∣ ∑ n ∈ F, W a M ∅ / n := by
  unfold res
  rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff, pow_one]

lemma mem_S_empty_iff {n : ℕ} :
    n ∈ S a M ∅ p 1 ↔ a < n ∧ n < M ∧ qpd a M ∅ p 1 ∣ n := by
  rw [S_eq_filter, V_empty_eq, Finset.mem_filter, Finset.mem_Ioo, and_assoc]

/-- **No selected endpoint in a mandatory first-digit layer.** -/
theorem firstDigit_mandatory_no_endpoint (ha : 0 < a) (h2a : 2 * a ≤ M) (hp : p.Prime)
    (he : 1 ≤ eW a M ∅ p) (hm : Mandatory a M ∅ p 1) :
    ¬ p ^ eW a M ∅ p ∣ a ∧ ¬ p ^ eW a M ∅ p ∣ M := by
  classical
  obtain ⟨hne, heta, hzs⟩ := (mandatory_iff_local ha hp (by omega : 1 ≤ eW a M ∅ p)).1 hm
  have hq1 := qpd_one (a := a) (M := M) (p := p) he
  set e := eW a M ∅ p
  set q := p ^ e with hqdef
  have hq0 : 0 < q := pow_pos hp.pos _
  have haM : a < M := by omega
  have haB : a ∈ B a M ∅ := mem_B.2 ⟨le_rfl, haM.le, by simp⟩
  have hMB : M ∈ B a M ∅ := mem_B.2 ⟨haM.le, le_rfl, by simp⟩
  have hmemB : ∀ n, a ≤ n → n ≤ M → n ∈ B a M ∅ := fun n h1 h2 => mem_B.2 ⟨h1, h2, by simp⟩
  have heta' : p ∣ ∑ n ∈ ({a, M} : Finset ℕ).filter (fun n => q ∣ n), W a M ∅ / n := by
    have := heta
    rw [eta, B_sdiff_V_empty haM.le, hq1] at this
    exact (sum_res_one_eq_zero_iff _).1 this
  have hzs' : ∀ G ⊆ S a M ∅ p 1, G.Nonempty → ¬ p ∣ ∑ n ∈ G, W a M ∅ / n := fun G hG hGne h =>
    hzs G hG hGne ((sum_res_one_eq_zero_iff G).2 h)
  have hS : ∀ n, n ∈ S a M ∅ p 1 ↔ a < n ∧ n < M ∧ q ∣ n := fun n => by
    rw [mem_S_empty_iff, hq1]
  by_contra hcon
  rw [not_and_or, not_not, not_not] at hcon
  by_cases hqa : q ∣ a <;> by_cases hqM : q ∣ M
  · -- both endpoints in the layer
    obtain ⟨ka, hka⟩ := hqa
    obtain ⟨kM, hkM⟩ := hqM
    have hfilt : ({a, M} : Finset ℕ).filter (fun n => q ∣ n) = {a, M} :=
      Finset.filter_true_of_mem (fun n hn => by
        rcases Finset.mem_insert.1 hn with rfl | hn
        · exact ⟨ka, hka⟩
        · rw [Finset.mem_singleton.1 hn]; exact ⟨kM, hkM⟩)
    rw [hfilt, Finset.sum_pair haM.ne, congrArg (W a M ∅ / ·) hka,
      congrArg (W a M ∅ / ·) hkM] at heta'
    have haB' : q * ka ∈ B a M ∅ := by rw [← hka]; exact haB
    have hMB' : q * kM ∈ B a M ∅ := by rw [← hkM]; exact hMB
    have hsum := (firstDigit_pair_iff ha hp haB' hMB').1 heta'
    have hlt : ka < kM := by
      by_contra h; push_neg at h
      have : q * kM ≤ q * ka := Nat.mul_le_mul_left _ h
      omega
    have h2k : 2 * ka ≤ kM := by
      have : q * (2 * ka) ≤ q * kM := by rw [← hkM]; linarith
      exact Nat.le_of_mul_le_mul_left this hq0
    have hka0 : 0 < ka := by
      rcases Nat.eq_zero_or_pos ka with h | h
      · rw [h, mul_zero] at hka; omega
      · exact h
    rcases (show kM = ka + 1 ∨ kM = ka + 2 ∨ ka + 3 ≤ kM by omega) with h1 | h2 | h3
    · -- `S = ∅`
      obtain ⟨n, hn⟩ := hne
      obtain ⟨h1', h2', ⟨j, rfl⟩⟩ := (hS n).1 hn
      rw [hka] at h1'
      rw [hkM] at h2'
      have : ka < j := Nat.lt_of_mul_lt_mul_left h1'
      have : j < kM := Nat.lt_of_mul_lt_mul_left h2'
      omega
    · -- `kM = ka + 2`: forces `p = 2` and a parity contradiction
      have hkB : q * (ka + 1) ∈ B a M ∅ := hmemB _ (by rw [hka]; nlinarith)
        (by rw [hkM]; nlinarith)
      have hnk := not_dvd_cofactor ha hp hkB
      have : ka + kM = 2 * (ka + 1) := by omega
      rw [this] at hsum
      rcases (Nat.Prime.dvd_mul hp).1 hsum with h | h
      · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
        have h1 := not_dvd_cofactor ha hp haB'
        rw [hp2] at h1 hnk
        omega
      · exact hnk h
    · -- `kM ≥ ka + 3`: the pair `q(ka+1)`, `q(kM-1)` is a zero-sum subfamily
      have hB1 : q * (ka + 1) ∈ B a M ∅ := hmemB _ (by rw [hka]; nlinarith)
        (by rw [hkM]; nlinarith)
      have hB2 : q * (kM - 1) ∈ B a M ∅ := hmemB _
        (by rw [hka]
            have : ka ≤ kM - 1 := by omega
            exact Nat.mul_le_mul_left _ this)
        (by rw [hkM]; exact Nat.mul_le_mul_left _ (by omega))
      have hne12 : q * (ka + 1) ≠ q * (kM - 1) := by
        intro h; have := Nat.eq_of_mul_eq_mul_left hq0 h; omega
      apply hzs' {q * (ka + 1), q * (kM - 1)} _ (Finset.insert_nonempty _ _)
      · rw [Finset.sum_pair hne12]
        rw [firstDigit_pair_iff ha hp hB1 hB2]
        have : ka + 1 + (kM - 1) = ka + kM := by omega
        rw [this]; exact hsum
      · intro n hn
        rw [hS]
        rcases Finset.mem_insert.1 hn with rfl | hn
        · refine ⟨by rw [hka]; exact Nat.mul_lt_mul_of_pos_left (by omega) hq0, ?_,
            dvd_mul_right _ _⟩
          rw [hkM]; exact Nat.mul_lt_mul_of_pos_left (by omega) hq0
        · rw [Finset.mem_singleton.1 hn]
          refine ⟨by rw [hka]; exact Nat.mul_lt_mul_of_pos_left (by omega) hq0, ?_,
            dvd_mul_right _ _⟩
          rw [hkM]; exact Nat.mul_lt_mul_of_pos_left (by omega) hq0
  · -- only `a` in the layer
    have hfilt : ({a, M} : Finset ℕ).filter (fun n => q ∣ n) = {a} := by
      ext n; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · exact absurd h hqM
      · rintro rfl; exact ⟨Or.inl rfl, hqa⟩
    rw [hfilt, Finset.sum_singleton] at heta'
    obtain ⟨ka, hka⟩ := hqa
    rw [congrArg (W a M ∅ / ·) hka] at heta'
    have haB' : q * ka ∈ B a M ∅ := by rw [← hka]; exact haB
    exact firstDigit_residue_ne_zero ha hp haB' heta'
  · -- only `M` in the layer
    have hfilt : ({a, M} : Finset ℕ).filter (fun n => q ∣ n) = {M} := by
      ext n; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · exact absurd h hqa
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, hqM⟩
    rw [hfilt, Finset.sum_singleton] at heta'
    obtain ⟨kM, hkM⟩ := hqM
    rw [congrArg (W a M ∅ / ·) hkM] at heta'
    have hMB' : q * kM ∈ B a M ∅ := by rw [← hkM]; exact hMB
    exact firstDigit_residue_ne_zero ha hp hMB' heta'
  · rcases hcon with h | h
    · exact hqa h
    · exact hqM h

/-- **Singleton mandatory first-digit coordinate**: it is `q` or `2q`. -/
theorem firstDigit_singleton (ha : 0 < a) (h2a : 2 * a ≤ M) (hp : p.Prime)
    (he : 1 ≤ eW a M ∅ p) (hm : Mandatory a M ∅ p 1) {n : ℕ} (hSn : S a M ∅ p 1 = {n}) :
    n = p ^ eW a M ∅ p ∨ n = 2 * p ^ eW a M ∅ p := by
  obtain ⟨hqa, hqM⟩ := firstDigit_mandatory_no_endpoint ha h2a hp he hm
  have hq1 := qpd_one (a := a) (M := M) (p := p) he
  set q := p ^ eW a M ∅ p
  have hq0 : 0 < q := pow_pos hp.pos _
  have hS : ∀ m, m ∈ S a M ∅ p 1 ↔ a < m ∧ m < M ∧ q ∣ m := fun m => by
    rw [mem_S_empty_iff, hq1]
  have hn : n ∈ S a M ∅ p 1 := by rw [hSn]; exact Finset.mem_singleton_self n
  obtain ⟨h1, h2, ⟨k, rfl⟩⟩ := (hS _).1 hn
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at h1; omega
    · exact h
  by_contra hcon
  have hk3 : 3 ≤ k := by
    by_contra h; push_neg at h
    interval_cases k
    · exact hcon (Or.inl (mul_one q))
    · exact hcon (Or.inr (mul_comm q 2))
  -- `q(k-1)` is not in the layer, so it is `≤ a`
  have hlow : q * (k - 1) ≤ a := by
    by_contra h; push_neg at h
    have hmem : q * (k - 1) ∈ S a M ∅ p 1 := (hS _).2 ⟨h, by
      have : q * (k - 1) < q * k := Nat.mul_lt_mul_of_pos_left (by omega) hq0
      omega, dvd_mul_right _ _⟩
    rw [hSn, Finset.mem_singleton] at hmem
    have := Nat.eq_of_mul_eq_mul_left hq0 hmem; omega
  -- `q(k+1)` is not in the layer, so it is `≥ M`, hence `> M`
  have hhigh : M < q * (k + 1) := by
    by_contra h; push_neg at h
    rcases h.lt_or_eq with h | h
    · have hmem : q * (k + 1) ∈ S a M ∅ p 1 := (hS _).2 ⟨by
        have : q * k < q * (k + 1) := Nat.mul_lt_mul_of_pos_left (by omega) hq0
        omega, h, dvd_mul_right _ _⟩
      rw [hSn, Finset.mem_singleton] at hmem
      have := Nat.eq_of_mul_eq_mul_left hq0 hmem; omega
    · exact hqM ⟨k + 1, h.symm⟩
  have : q * (k + 1) ≤ q * (2 * (k - 1)) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

end Erdos287.PostQSigma
