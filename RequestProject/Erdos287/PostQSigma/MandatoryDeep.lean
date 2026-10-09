import RequestProject.Erdos287.PostQSigma.FirstDigit
import RequestProject.Erdos287.PostQSigma.RawSource

/-!
# Erdős #287 — post-`Q_Σ` bank, §11 (V57): all-`M` deep mandatory classification

**Status: BANK (proved in Lean, all `M`).**

`deep_mandatory_classification`: for the raw source `(a, M)` with `a ≥ 1` and `H(a, M) ≥ 1`,
if a physical prime-depth layer `S_{p,d}` with `d ≥ 2` is mandatory then
`(p, d) ∈ {(2,2), (2,3), (3,2), (5,2)}`.

Proof (all-`M`, no census):
1. *harmonic bound* — `e·(a-1) < M` (`exp_mul_pred_lt_of_harmonic`), used as
   `2718 (a - 1) < 1000 M`;
2. *cofactor count* — `p^e ≤ M` (`pow_eW_le`), so the cofactor row
   `{k : a < qk < M}` (`q = p^{e-d+1}`) is long;
3. *zero-sum pair* — two cofactors `k ≠ k'` prime to `p` with `p ∣ k + k'` give
   `W/(qk) + W/(qk') ≡ 0 (mod p^d)` (`res_pair_zero`), so the layer is not zero-sum free;
   such a pair exists (`pair_exists`) by a window argument (`p = 2, d ≥ 4`; odd `p, d ≥ 3`;
   `p ≥ 7, d = 2` with a long row) or the explicit pairs `(s+1, p-s-1)` / `(p-1, p+1)`
   (`p ≥ 7, d = 2`, short row);
4. *finite terminal cases* — the only escape of step 3 is `p = 7`, `q = 7`, `a = 21`,
   `M ∈ {55, 56}`; `H(21,55) < 1` and, for `M = 56`, the endpoint term `η_{7,2} ≠ 0`
   (both kernel-checked by `norm_num` / `decide`).

**Audit finding.**  The hypothesis `H(a,M) ≥ 1` cannot be weakened to `2a ≤ M`: e.g.
`(a, M) = (22, 50)` has a mandatory `(7, 2)` layer (exhibited by exhaustive search during the
audit; the Lean statement keeps the stronger, correct hypothesis).
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- The four exceptional deep coordinates. -/
def deepExceptions : Finset (ℕ × ℕ) := {(2, 2), (2, 3), (3, 2), (5, 2)}

/-! ### Step 2: `p^e ≤ M` -/

/-- A prime power dividing the lcm of a set of positive integers divides one of them. -/
lemma exists_mem_pow_dvd_lcm {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ≠ 0) (h : p ^ k ∣ s.lcm id) : ∃ n ∈ s, p ^ k ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty, Nat.dvd_one] at h
    exact absurd h (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  | insert n s hn ih =>
    rw [Finset.lcm_insert] at h
    change p ^ k ∣ Nat.lcm n (s.lcm id) at h
    have hn0 : n ≠ 0 := hs n (Finset.mem_insert_self _ _)
    have hL0 : s.lcm id ≠ 0 := by
      rw [Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨x, hx, hx0⟩
      exact hs x (Finset.mem_insert_of_mem hx) hx0
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hn0 hL0), Nat.factorization_lcm hn0 hL0,
      Finsupp.sup_apply, le_max_iff] at h
    rcases h with h | h
    · exact ⟨n, Finset.mem_insert_self _ _, (hp.pow_dvd_iff_le_factorization hn0).2 h⟩
    · obtain ⟨m, hm, hdm⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
        ((hp.pow_dvd_iff_le_factorization hL0).2 h)
      exact ⟨m, Finset.mem_insert_of_mem hm, hdm⟩

/-- `p^e ≤ M` for `e = v_p(W) ≥ 1`. -/
lemma pow_eW_le {a M p : ℕ} (ha : 0 < a) (hp : p.Prime) (he : 1 ≤ eW a M ∅ p) :
    p ^ eW a M ∅ p ≤ M := by
  obtain ⟨n, hn, hdn⟩ := exists_mem_pow_dvd_lcm hp he (B a M ∅)
    (fun n hn => (pos_of_mem_B ha hn).ne') (Nat.ordProj_dvd (W a M ∅) p)
  exact (Nat.le_of_dvd (pos_of_mem_B ha hn) hdn).trans (mem_B.1 hn).2.1

/-! ### Step 3a: zero-sum pairs -/

/-- **Zero-sum pair**: two cofactors prime to `p` with `p ∣ k + k'` give a zero-sum pair of
residues modulo `p^d` in the layer `S_{p,d}`. -/
lemma res_pair_zero {a M p d : ℕ} (ha : 0 < a) (hp : p.Prime) (hd1 : 1 ≤ d)
    (hd : d ≤ eW a M ∅ p) {k1 k2 : ℕ} (hB1 : qpd a M ∅ p d * k1 ∈ B a M ∅)
    (hB2 : qpd a M ∅ p d * k2 ∈ B a M ∅) (h1 : ¬ p ∣ k1) (h2 : ¬ p ∣ k2) (h12 : p ∣ k1 + k2) :
    res a M ∅ p d (qpd a M ∅ p d * k1) + res a M ∅ p d (qpd a M ∅ p d * k2) = 0 := by
  set e := eW a M ∅ p
  set q := qpd a M ∅ p d with hqdef
  set W0 := W a M ∅
  have hW0 : W0 ≠ 0 := W_ne_zero ha
  set U := W0 / p ^ e
  have hWU : p ^ e * U = W0 := Nat.ordProj_mul_ordCompl_eq_self W0 p
  have hU : ¬ p ∣ U := Nat.not_dvd_ordCompl hp hW0
  have hq : q * p ^ (d - 1) = p ^ e := by
    rw [hqdef, qpd, ← pow_add]; congr 1; omega
  have hqpos : 0 < q := pow_pos hp.pos _
  have hDpos : 0 < p ^ (d - 1) := pow_pos hp.pos _
  -- each cofactor
  have key : ∀ k, q * k ∈ B a M ∅ → ¬ p ∣ k →
      ∃ u, W0 / (q * k) = p ^ (d - 1) * u ∧ k * u = U := by
    intro k hB hk
    obtain ⟨m, hm⟩ : q * k ∣ W0 := dvd_W_of_mem_B hB
    have hkpos : 0 < q * k := pos_of_mem_B ha hB
    have hdiv : W0 / (q * k) = m := by rw [hm, Nat.mul_div_cancel_left _ hkpos]
    have h1 : q * (p ^ (d - 1) * U) = q * (k * m) := by
      rw [← mul_assoc, hq, hWU, hm, mul_assoc]
    have h2 : p ^ (d - 1) * U = k * m := Nat.eq_of_mul_eq_mul_left hqpos h1
    have hcop : Nat.Coprime (p ^ (d - 1)) k :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
    obtain ⟨u, hu⟩ : p ^ (d - 1) ∣ m :=
      hcop.dvd_of_dvd_mul_left ⟨U, by rw [← h2]⟩
    refine ⟨u, by rw [hdiv, hu], ?_⟩
    have : p ^ (d - 1) * U = p ^ (d - 1) * (k * u) := by rw [h2, hu]; ring
    exact (Nat.eq_of_mul_eq_mul_left hDpos this).symm
  obtain ⟨u1, hu1, hk1⟩ := key k1 hB1 h1
  obtain ⟨u2, hu2, hk2⟩ := key k2 hB2 h2
  have hpu : p ∣ u1 + u2 := by
    have : (u1 + u2) * (k1 * k2) = U * (k1 + k2) := by
      calc (u1 + u2) * (k1 * k2) = (k1 * u1) * k2 + (k2 * u2) * k1 := by ring
        _ = U * k2 + U * k1 := by rw [hk1, hk2]
        _ = U * (k1 + k2) := by ring
    have hdvd : p ∣ (u1 + u2) * (k1 * k2) := by rw [this]; exact Dvd.dvd.mul_left h12 _
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd h h1
      · exact absurd h h2
  unfold res
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff, hu1, hu2, ← mul_add]
  obtain ⟨c, hc⟩ := hpu
  rw [hc, ← mul_assoc, ← pow_succ, show d - 1 + 1 = d by omega]
  exact dvd_mul_right _ _

/-! ### Step 3b: existence of a pair -/

lemma window_odd {p : ℕ} (hp3 : 3 ≤ p) (m : ℕ) :
    ∃ k1 k2, m ≤ k1 ∧ k1 ≤ m + p - 1 ∧ m ≤ k2 ∧ k2 ≤ m + p - 1 ∧ k1 ≠ k2 ∧ ¬ p ∣ k1 ∧
      ¬ p ∣ k2 ∧ p ∣ k1 + k2 := by
  have h1 := Nat.div_add_mod (m + p - 2) p
  have h1' := Nat.mod_lt (m + p - 2) (by omega : p > 0)
  have h2 := Nat.div_add_mod m p
  have h2' := Nat.mod_lt m (by omega : p > 0)
  set c1 := (m + p - 2) / p
  set c2 := m / p
  have hk1 : (p * c1 + 1) % p = 1 := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  have hk2 : (p * c2 + (p - 1)) % p = p - 1 := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  have hsum : p ∣ (p * c1 + 1) + (p * c2 + (p - 1)) :=
    ⟨c1 + c2 + 1, by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega⟩
  refine ⟨p * c1 + 1, p * c2 + (p - 1), by omega, by omega, by omega, by omega, ?_, ?_, ?_, hsum⟩
  · intro h; rw [h] at hk1; omega
  · intro h; rw [Nat.dvd_iff_mod_eq_zero] at h; omega
  · intro h; rw [Nat.dvd_iff_mod_eq_zero] at h; omega

lemma window_two (m : ℕ) :
    ∃ k1 k2, m ≤ k1 ∧ k1 ≤ m + 3 ∧ m ≤ k2 ∧ k2 ≤ m + 3 ∧ k1 ≠ k2 ∧ ¬ 2 ∣ k1 ∧
      ¬ 2 ∣ k2 ∧ 2 ∣ k1 + k2 :=
  ⟨2 * (m / 2) + 1, 2 * (m / 2) + 3, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

/-- A window of cofactors `[⌊a/q⌋+1, ⌊a/q⌋+L]` lies in the physical row when `a + qL < M`. -/
lemma window_mem {q a M L k : ℕ} (hq : 0 < q) (h : a + q * L < M) (hk1 : a / q + 1 ≤ k)
    (hk2 : k ≤ a / q + L) : a < q * k ∧ q * k < M := by
  have h1 : a < q * (a / q + 1) := Nat.lt_mul_div_succ a hq
  have h2 : q * (a / q) ≤ a := Nat.mul_div_le a q
  constructor
  · exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left q hk1)
  · calc q * k ≤ q * (a / q + L) := Nat.mul_le_mul_left q hk2
      _ = q * (a / q) + q * L := by ring
      _ < M := by omega

/-- **Pair existence** for every non-exceptional deep coordinate (pure arithmetic). -/
lemma pair_exists {p d j a M : ℕ} (hp : p.Prime) (hd2 : 2 ≤ d) (hj : 1 ≤ j)
    (hnot : (p, d) ∉ deepExceptions) (hPM : p ^ j * p ^ (d - 1) ≤ M)
    (hA : 2718 * (a - 1) < 1000 * M)
    (hspec : ¬ (p = 7 ∧ d = 2 ∧ p ^ j = 7 ∧ a = 21 ∧ (M = 55 ∨ M = 56))) :
    ∃ k1 k2, k1 ≠ k2 ∧ a < p ^ j * k1 ∧ p ^ j * k1 < M ∧ a < p ^ j * k2 ∧ p ^ j * k2 < M ∧
      ¬ p ∣ k1 ∧ ¬ p ∣ k2 ∧ p ∣ k1 + k2 := by
  have hpq : p ≤ p ^ j := Nat.le_self_pow (by omega) p
  generalize hqdef : p ^ j = q at *
  have hp2 := hp.two_le
  have hqpos : 0 < q := by omega
  simp only [deepExceptions, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    not_or, not_and] at hnot
  obtain ⟨n22, n23, n32, n52⟩ := hnot
  rcases eq_or_ne p 2 with rfl | hp2'
  · -- `p = 2`, `d ≥ 4`
    have hd4 : 4 ≤ d := by
      have := n22 rfl; have := n23 rfl; omega
    have hD : 2 ^ 3 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8 : q * 8 ≤ M := le_trans (Nat.mul_le_mul_left q (by simpa using hD)) hPM
    have hw : a + q * 4 < M := by omega
    obtain ⟨k1, k2, a1, b1, a2, b2, hne, h1, h2, h12⟩ := window_two (a / q + 1)
    obtain ⟨c1, d1⟩ := window_mem hqpos hw a1 (by omega)
    obtain ⟨c2, d2⟩ := window_mem hqpos hw a2 (by omega)
    exact ⟨k1, k2, hne, c1, d1, c2, d2, h1, h2, h12⟩
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2'
  have hp3 : 3 ≤ p := by omega
  have hwin : a + q * p < M → ∃ k1 k2, k1 ≠ k2 ∧ a < q * k1 ∧ q * k1 < M ∧ a < q * k2 ∧
      q * k2 < M ∧ ¬ p ∣ k1 ∧ ¬ p ∣ k2 ∧ p ∣ k1 + k2 := by
    intro hw
    obtain ⟨k1, k2, a1, b1, a2, b2, hne, h1, h2, h12⟩ := window_odd hp3 (a / q + 1)
    obtain ⟨c1, d1⟩ := window_mem hqpos hw a1 (by omega)
    obtain ⟨c2, d2⟩ := window_mem hqpos hw a2 (by omega)
    exact ⟨k1, k2, hne, c1, d1, c2, d2, h1, h2, h12⟩
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hd3
  · -- `d = 2`, `p ≥ 7`
    have hp7 : 7 ≤ p := by
      have h3 : p ≠ 3 := fun h => n32 h rfl
      have h5 : p ≠ 5 := fun h => n52 h rfl
      rcases (show p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ 7 ≤ p by omega) with h | h | h | h | h
      · exact absurd h h3
      · exact absurd (h ▸ hp) (by norm_num)
      · exact absurd h h5
      · exact absurd (h ▸ hp) (by norm_num)
      · exact h
    have hX : q * p ≤ M := by simpa using hPM
    by_cases hw : a + q * p < M
    · exact hwin hw
    push_neg at hw
    clear hwin
    have hqs : q * (a / q) ≤ a := Nat.mul_div_le a q
    have has : a < q * (a / q + 1) := Nat.lt_mul_div_succ a hqpos
    generalize a / q = s at hqs has
    have hq7 : q * 7 ≤ q * p := Nat.mul_le_mul_left q hp7
    have hqp1 : q * (p - 1) + q = q * p := by
      rw [← Nat.mul_succ]; congr 1; omega
    by_cases hb1 : 2 * s + 3 ≤ p
    · -- the pair `(s+1, p-s-1)` with sum `p`
      have m1 : q * (s + 2) ≤ q * (p - s - 1) := Nat.mul_le_mul_left q (by omega)
      have m2 : q * (p - s - 1) ≤ q * (p - 1) := Nat.mul_le_mul_left q (by omega)
      have m3 : q * (s + 1) ≤ q * (p - s - 1) := Nat.mul_le_mul_left q (by omega)
      have e1 : q * (s + 2) = q * (s + 1) + q := by ring
      refine ⟨s + 1, p - s - 1, by omega, has, by omega, by omega, by omega,
        Nat.not_dvd_of_pos_of_lt (by omega) (by omega),
        Nat.not_dvd_of_pos_of_lt (by omega) (by omega), ⟨1, by omega⟩⟩
    · -- the pair `(p-1, p+1)` with sum `2p`
      have hs2 : s + 2 ≤ p := by
        by_contra hc
        have : q * (p - 1) ≤ q * s := Nat.mul_le_mul_left q (by omega)
        omega
      have h2s : q * (p - 1) ≤ 2 * (q * s) := by
        rw [← mul_assoc, mul_comm 2 q, mul_assoc]; exact Nat.mul_le_mul_left q (by omega)
      have e2 : q * (p + 1) = q * p + q := by ring
      have hright : q * (p + 1) < M := by
        by_contra hc
        push_neg at hc
        have hp10 : p ≤ 10 := by
          by_contra hc'
          have : q * 11 ≤ q * p := Nat.mul_le_mul_left q (by omega)
          omega
        have hp7' : p = 7 := by
          interval_cases p <;> first | rfl | exact absurd hp (by norm_num)
        subst hp7'
        have hq17 : q ≤ 17 := by omega
        have hq7 : q = 7 := by
          rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
          · simp at hqdef; omega
          · have : 7 ^ 2 ≤ 7 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
            omega
        rw [hq7] at hqs has hX hc h2s hw
        exact hspec ⟨rfl, rfl, hq7, by omega, by omega⟩
      have m1 : q * (s + 1) ≤ q * (p - 1) := Nat.mul_le_mul_left q (by omega)
      have hpm1 : ¬ p ∣ p - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have hpp1 : ¬ p ∣ p + 1 := by
        intro h
        have := (Nat.dvd_add_right (dvd_refl p)).1 h
        exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      refine ⟨p - 1, p + 1, by omega, by omega, by omega, by omega, hright, hpm1, hpp1,
        ⟨2, by omega⟩⟩
  · -- odd `p`, `d ≥ 3`
    have hD : p ^ 2 ≤ p ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : q * p * 3 ≤ M := by
      calc q * p * 3 ≤ q * p * p := Nat.mul_le_mul_left _ hp3
        _ = q * p ^ 2 := by ring
        _ ≤ q * p ^ (d - 1) := Nat.mul_le_mul_left q hD
        _ ≤ M := hPM
    have h9 : 3 * 3 ≤ q * p := Nat.mul_le_mul (hp3.trans hpq) hp3
    exact hwin (by omega)

/-! ### Step 4: the finite terminal cases -/

lemma Hm_21_55 : Hm 21 55 < 1 := by
  unfold Hm
  rw [show Finset.Icc 21 55 = Finset.Ico 21 56 from rfl]
  simp only [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ]

lemma eta_21_56_num : ¬ (7 ^ 2 ∣ W 21 56 ∅ / 21 + W 21 56 ∅ / 56) := by decide

/-! ### The classification -/

/-- From `H(a, M) ≥ 1`: `2718 (a - 1) < 1000 M`. -/
lemma harmonic_rational_bound {a M : ℕ} (ha : 0 < a) (hM : 0 < M) (hH : 1 ≤ Hm a M) :
    2718 * (a - 1) < 1000 * M := by
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · simp; omega
  have h := exp_mul_pred_lt_of_harmonic ha2 hH
  have he : (2718 : ℝ) / 1000 < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hpos : (0 : ℝ) ≤ (a : ℝ) - 1 := by rw [← ha1]; positivity
  have : ((2718 * (a - 1) : ℕ) : ℝ) < ((1000 * M : ℕ) : ℝ) := by
    push_cast; rw [ha1]; nlinarith
  exact_mod_cast this

/-- **V57 all-`M` deep mandatory classification.** -/
theorem deep_mandatory_classification {a M p d : ℕ} (ha : 0 < a) (hH : 1 ≤ Hm a M)
    (hp : p.Prime) (hd2 : 2 ≤ d) (hd : d ≤ eW a M ∅ p) (hm : Mandatory a M ∅ p d) :
    (p, d) ∈ deepExceptions := by
  classical
  by_contra hnot
  obtain ⟨hne, heta, hzs⟩ := (mandatory_iff_local ha hp hd).1 hm
  set e := eW a M ∅ p
  set j := e - d + 1 with hjdef
  have hqj : qpd a M ∅ p d = p ^ j := rfl
  have hM : 0 < M := by
    obtain ⟨n, hn⟩ := hne
    have := (Finset.mem_Ioo.1 (by rw [← V_empty_eq]; exact (Finset.mem_filter.1 hn).1)).2
    omega
  have hA := harmonic_rational_bound ha hM hH
  have hPM : p ^ j * p ^ (d - 1) ≤ M := by
    rw [← pow_add, show j + (d - 1) = e by omega]
    exact pow_eW_le ha hp (by omega)
  have hS : S a M ∅ p d = (cofInt a M (p ^ j)).image (fun k => p ^ j * k) := by
    rw [S_empty_eq_cofactor_image hp, hqj]
  by_cases hspec : p = 7 ∧ d = 2 ∧ p ^ j = 7 ∧ a = 21 ∧ (M = 55 ∨ M = 56)
  · obtain ⟨rfl, rfl, hq7, rfl, hM'⟩ := hspec
    rcases hM' with rfl | rfl
    · exact absurd hH (not_le.2 Hm_21_55)
    · apply eta_21_56_num
      have hBV := B_sdiff_V_empty (a := 21) (M := 56) (by norm_num)
      rw [eta, hBV, hqj, hq7] at heta
      rw [Finset.filter_true_of_mem (by intro n hn; simp at hn; rcases hn with rfl | rfl <;>
        norm_num), Finset.sum_pair (by norm_num)] at heta
      unfold res at heta
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at heta
      exact heta
  obtain ⟨k1, k2, hne12, a1, b1, a2, b2, h1, h2, h12⟩ :=
    pair_exists hp hd2 (by omega) hnot hPM hA hspec
  have hmem : ∀ k, a < p ^ j * k → p ^ j * k < M → k ∈ cofInt a M (p ^ j) := by
    intro k h1 h2
    simp only [cofInt, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, h1, h2⟩
    have : k ≤ p ^ j * k := Nat.le_mul_of_pos_left k (pow_pos hp.pos _)
    omega
  have hB : ∀ k, a < p ^ j * k → p ^ j * k < M → qpd a M ∅ p d * k ∈ B a M ∅ := by
    intro k h1 h2
    rw [hqj]; exact mem_B.2 ⟨by omega, by omega, by simp⟩
  have hinj : p ^ j * k1 ≠ p ^ j * k2 := fun h =>
    hne12 (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h)
  apply hzs {p ^ j * k1, p ^ j * k2}
  · intro n hn
    rw [hS, Finset.mem_image]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact ⟨k1, hmem k1 a1 b1, rfl⟩
    · exact ⟨k2, hmem k2 a2 b2, rfl⟩
  · exact ⟨_, Finset.mem_insert_self _ _⟩
  · rw [Finset.sum_pair hinj]
    have := res_pair_zero ha hp (by omega) hd (hB k1 a1 b1) (hB k2 a2 b2) h1 h2 h12
    rwa [hqj] at this

end Erdos287.PostQSigma

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-! ### Audit counterfixture: `2a ≤ M` alone does not suffice -/

lemma eW_22_50_7 : eW 22 50 ∅ 7 = 2 := by
  have hW : W 22 50 ∅ ≠ 0 := W_ne_zero (by norm_num)
  have hp : Nat.Prime 7 := by norm_num
  have h2 : 7 ^ 2 ∣ W 22 50 ∅ := by decide
  have h3 : ¬ 7 ^ 3 ∣ W 22 50 ∅ := by decide
  rw [hp.pow_dvd_iff_le_factorization hW] at h2 h3
  unfold eW; omega

/-- **Diagnostic counterfixture (audit finding).**  For `(a, M) = (22, 50)` we have `2a ≤ M`
but `H(22, 50) < 1`, and the depth-2 layer of `p = 7` is mandatory although `(7, 2)` is not in
the exceptional list.  Hence the classification genuinely needs `H(a, M) ≥ 1`. -/
theorem deep_classification_needs_harmonic :
    2 * 22 ≤ 50 ∧ Hm 22 50 < 1 ∧ Mandatory 22 50 ∅ 7 2 ∧ (7, 2) ∉ deepExceptions := by
  classical
  have hp : Nat.Prime 7 := by norm_num
  have he := eW_22_50_7
  have hq : qpd 22 50 ∅ 7 2 = 7 := by rw [qpd, he]; norm_num
  have hS : S 22 50 ∅ 7 2 = {28, 35, 42, 49} := by
    rw [S_eq_filter, hq, V_empty_eq]; decide
  refine ⟨by norm_num, ?_, ?_, by decide⟩
  · unfold Hm
    rw [show Finset.Icc 22 50 = Finset.Ico 22 51 from rfl]
    simp only [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  · refine (mandatory_iff_local (by norm_num) hp (by rw [he])).2 ⟨?_, ?_, ?_⟩
    · rw [hS]; decide
    · rw [eta, B_sdiff_V_empty (by norm_num), hq]
      rw [Finset.filter_false_of_mem (by intro n hn; simp at hn; rcases hn with rfl | rfl <;>
        norm_num), Finset.sum_empty]
    · rw [hS]
      intro G hG hne
      have hG' : G ∈ ({28, 35, 42, 49} : Finset ℕ).powerset := Finset.mem_powerset.2 hG
      unfold res
      revert hne
      revert G
      decide

end Erdos287.PostQSigma
