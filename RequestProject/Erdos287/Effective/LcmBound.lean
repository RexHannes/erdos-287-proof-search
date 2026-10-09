import RequestProject.Erdos287.Effective.Hinge

/-!
# Erdős #287 — the universal bound `lcm(1,…,h) ≤ 4^{h-1}` and the logarithmic height

**ERDŐS #287 REMAINS OPEN.**

* `prime_dvd_choose_of_window` — if `k ≤ n ≤ 2k` and `k < p^a ≤ n` (`a ≥ 1`), then
  `p ∣ C(n, k)` (Kummer: a carry at position `a`).
* `Lh_dvd_Lh_mul_choose` — `L_n ∣ L_k · C(n, k)` for `k ≤ n ≤ 2k`.
* `Lh_le_four_pow` — **`lcm(1,…,h) ≤ 4^{h-1}` for every `h`** (with `4^{0-1} = 1`), by
  `L_{2m} ≤ L_m C(2m,m)` and `L_{2m+1} ≤ L_{m+1} C(2m+1,m+1)`, `C(2m+1,m) ≤ 4^m`.
* consequences (no `LcmBound3` hypothesis): `mul_Bh_lt_eight_pow` (`h B_h < 8^h`),
  `log_height` (`8^h ≤ M ⇒ h ≤ H_*(M)`), `log_height_nine` (the former conditional statement
  `9^h < M ⇒ h ≤ H_*(M)` **without** the hypothesis `LcmBound3`), and the logarithmic-height
  criterion `log_height_real` (`h ≤ log M / log 8 ⇒ h ≤ H_*(M)`) and `floor_log_le_Hstar`
  (`⌊log M / log 8⌋ ≤ H_*(M)` for `M ≥ 1`).
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Effective

/-- Kummer: a carry at position `a`. -/
theorem prime_dvd_choose_of_window {p n k a : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hn2 : n ≤ 2 * k)
    (ha : 1 ≤ a)
    (hk : k < p ^ a) (hn : p ^ a ≤ n) : p ∣ n.choose k := by
  have hnk : n - k < p ^ a := by omega
  have hc : 0 < n.choose k := Nat.choose_pos hkn
  rw [hp.dvd_iff_one_le_factorization hc.ne',
    Nat.factorization_choose hp hkn (Nat.lt_succ_self (Nat.log p n))]
  apply Finset.card_pos.2
  refine ⟨a, ?_⟩
  rw [mem_filter, mem_Ico, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hnk]
  refine ⟨⟨ha, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hn)⟩, ?_⟩
  rw [Nat.add_sub_cancel' hkn]; exact hn

theorem mem_Icc_Lh {j h : ℕ} (hj1 : 1 ≤ j) (hjh : j ≤ h) : j ∣ Lh h :=
  dvd_Lh (mem_Icc.2 ⟨hj1, hjh⟩)

/-- **`L_n ∣ L_k · C(n, k)` for `k ≤ n ≤ 2k`.** -/
theorem Lh_dvd_Lh_mul_choose {n k : ℕ} (hkn : k ≤ n) (hn2 : n ≤ 2 * k) :
    Lh n ∣ Lh k * n.choose k := by
  have hX : Lh k * n.choose k ≠ 0 :=
    Nat.mul_ne_zero (Lh_pos k).ne' (Nat.choose_pos hkn).ne'
  unfold Lh
  refine Finset.lcm_dvd (fun j hj => ?_)
  obtain ⟨hj1, hjn⟩ := mem_Icc.1 hj
  have hj0 : j ≠ 0 := by omega
  change j ∣ Lh k * n.choose k
  rw [← Nat.factorization_prime_le_iff_dvd hj0 hX]
  intro p hp
  set a := j.factorization p with ha
  rcases Nat.eq_zero_or_pos a with h0 | hapos
  · rw [h0]; exact Nat.zero_le _
  rw [← hp.pow_dvd_iff_le_factorization hX]
  have hpa_dvd : p ^ a ∣ j := Nat.ordProj_dvd j p
  have hpa_le : p ^ a ≤ n := (Nat.le_of_dvd (by omega) hpa_dvd).trans hjn
  rcases Nat.lt_or_ge k (p ^ a) with hk | hk
  · -- `p^{a-1} ≤ k` and `p ∣ C(n,k)`
    have hsplit : p ^ a = p ^ (a - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    have h2 : 2 * p ^ (a - 1) ≤ p ^ a := by
      rw [hsplit, mul_comm]; exact Nat.mul_le_mul_left _ hp.two_le
    have hle : p ^ (a - 1) ≤ k := by omega
    have hpos : 1 ≤ p ^ (a - 1) := Nat.one_le_pow _ _ hp.pos
    rw [hsplit]
    exact Nat.mul_dvd_mul (mem_Icc_Lh hpos hle)
      (prime_dvd_choose_of_window hp hkn hn2 hapos hk hpa_le)
  · exact Dvd.dvd.mul_right (mem_Icc_Lh (Nat.one_le_pow _ _ hp.pos) hk) _

lemma Lh_zero : Lh 0 = 1 := by decide

lemma Lh_one : Lh 1 = 1 := by decide

/-- **`lcm(1, …, h) ≤ 4^{h-1}`** for every `h` (with natural subtraction, `4^{0-1} = 1`). -/
theorem Lh_le_four_pow (h : ℕ) : Lh h ≤ 4 ^ (h - 1) := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    rcases Nat.lt_or_ge h 2 with hlt | hge
    · interval_cases h
      · simp [Lh_zero]
      · simp [Lh_one]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' h
    · -- `h = 2m`, `m ≥ 1`
      have hm : 1 ≤ m := by omega
      have h1 : Lh (2 * m) ≤ Lh m * (2 * m).choose m :=
        Nat.le_of_dvd (Nat.mul_pos (Lh_pos m) (Nat.choose_pos (by omega)))
          (Lh_dvd_Lh_mul_choose (by omega) le_rfl)
      have h2 : (2 * m).choose m ≤ 4 ^ m :=
        (Nat.choose_le_choose m (Nat.le_succ _)).trans (Nat.choose_middle_le_pow m)
      have h3 := ih m (by omega)
      calc Lh (2 * m) ≤ Lh m * (2 * m).choose m := h1
        _ ≤ 4 ^ (m - 1) * 4 ^ m := Nat.mul_le_mul h3 h2
        _ = 4 ^ (2 * m - 1) := by rw [← pow_add]; congr 1; omega
    · -- `h = 2m + 1`, `m ≥ 1`
      have hm : 1 ≤ m := by omega
      have h1 : Lh (2 * m + 1) ≤ Lh (m + 1) * (2 * m + 1).choose (m + 1) :=
        Nat.le_of_dvd (Nat.mul_pos (Lh_pos _) (Nat.choose_pos (by omega)))
          (Lh_dvd_Lh_mul_choose (by omega) (by omega))
      have h2 : (2 * m + 1).choose (m + 1) ≤ 4 ^ m := by
        rw [Nat.choose_symm_half]; exact Nat.choose_middle_le_pow m
      have h3 := ih (m + 1) (by omega)
      calc Lh (2 * m + 1) ≤ Lh (m + 1) * (2 * m + 1).choose (m + 1) := h1
        _ ≤ 4 ^ (m + 1 - 1) * 4 ^ m := Nat.mul_le_mul h3 h2
        _ = 4 ^ (2 * m + 1 - 1) := by rw [← pow_add]; congr 1; omega

lemma sq_lt_four_mul_two_pow (h : ℕ) : h ^ 2 < 4 * 2 ^ h := by
  induction h with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> norm_num
    · rw [pow_succ 2]
      nlinarith

/-- **`h B_h < 8^h`** for every `h` (unconditional). -/
theorem mul_Bh_lt_eight_pow (h : ℕ) : h * Bh h < 8 ^ h := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp
  have hL := Lh_le_four_pow h
  have hsq := sq_lt_four_mul_two_pow h
  have e4 : 4 ^ h = 4 * 4 ^ (h - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e8 : (8 : ℕ) ^ h = 2 ^ h * 4 ^ h := by rw [← mul_pow]; norm_num
  calc h * Bh h ≤ h * (h * Lh h) := Nat.mul_le_mul_left _ (Bh_le h)
    _ = h ^ 2 * Lh h := by ring
    _ ≤ h ^ 2 * 4 ^ (h - 1) := Nat.mul_le_mul_left _ hL
    _ < 8 ^ h := by
      rw [e8, e4]
      have hp : 0 < 4 ^ (h - 1) := by positivity
      nlinarith

/-- **Logarithmic height** (unconditional): `8^h ≤ M ⇒ h ≤ H_*(M)`. -/
theorem log_height {M h : ℕ} (hM : 8 ^ h ≤ M) : h ≤ Hstar M :=
  le_Hstar (lt_of_lt_of_le (mul_Bh_lt_eight_pow h) hM)

/-- The former conditional statement, now **without** the hypothesis `LcmBound3`:
`9^h < M ⇒ h ≤ H_*(M)`. -/
theorem log_height_nine {M h : ℕ} (hM : 9 ^ h < M) : h ≤ Hstar M :=
  log_height ((Nat.pow_le_pow_left (by norm_num) h).trans hM.le)

/-- **Logarithmic-height criterion**: for `M ≥ 1`, `h ≤ log M / log 8 ⇒ h ≤ H_*(M)`. -/
theorem log_height_real {M h : ℕ} (hM : 1 ≤ M)
    (hh : (h : ℝ) ≤ Real.log M / Real.log 8) : h ≤ Hstar M := by
  refine log_height ?_
  have hl8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [le_div_iff₀ hl8] at hh
  have : (8 : ℝ) ^ h ≤ M := by
    rw [← Real.exp_log hM0, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    linarith
  exact_mod_cast this

/-- `⌊log M / log 8⌋ ≤ H_*(M)` for `M ≥ 1`. -/
theorem floor_log_le_Hstar {M : ℕ} (hM : 1 ≤ M) :
    ⌊Real.log M / Real.log 8⌋₊ ≤ Hstar M := by
  refine log_height_real hM (Nat.floor_le ?_)
  exact div_nonneg (Real.log_natCast_nonneg M) (Real.log_nonneg (by norm_num))

end Erdos287.Effective
