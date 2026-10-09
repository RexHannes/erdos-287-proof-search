import RequestProject.Erdos287.ResearchBankV8.WeakCutoffSeed

/-!
# Erdős #287 — Research Bank V8 §2E: the exact prime-power ENTRY system

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For an owner prime `p` with first `p`-power above the cutoff `Q_p = p^s` (`p^(s-1) ≤ T < p^s`),

  `m_p = ⌊M / Q_p⌋`,  `J_p = L_{m_p} = lcm(1,…,m_p)`,  `r_p = v_p(J_p)`,  `d_p = p^(r_p+1)`,

and the **full row congruence**

  `∑_{Q_p c ∈ I} x_{Q_p c} · (J_p / c) ≡ 0 (mod d_p)`.

Kernel-proved here (`pLocal_entry_iff_row_congruence`): for any finite `I ⊆ [1, M]` and any word
`x`, the `p`-local denominator-entry condition

  `p^(s-1) · ∑_{n ∈ I, x_n = 1} 1/n` is `p`-integral

(which is exactly the `p`-part of "the reduced denominator divides `L_T`", since
`v_p(L_T) = s − 1`) holds **iff** the full row congruence modulo `d_p = p^(r_p+1)` holds.

The precision is the full prime power `p^(r_p+1)`, never merely `p`.  **Firewall**
(`top_digit_insufficient`): at `p = 2`, `T = 3`, `Q = 4`, `M = 12`, `I = {4}` the row sum is
`J/1 = 6`, which is `≡ 0 (mod 2)` (top digit passes) but `≢ 0 (mod 4)`, and the entry condition
genuinely fails.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace ExactEntrySystem

open Saturation WeakCutoffSeed

/-! ## 1.  `p`-integral rationals -/

/-- `q` is `p`-integral: `q · v ∈ ℤ` for some `v` coprime to `p`. -/
def PInt (p : ℕ) (q : ℚ) : Prop := ∃ u : ℤ, ∃ v : ℕ, Nat.Coprime p v ∧ q * v = u

theorem PInt.int (p : ℕ) (z : ℤ) : PInt p z := ⟨z, 1, Nat.coprime_one_right _, by simp⟩

theorem PInt.add {p : ℕ} {a b : ℚ} (ha : PInt p a) (hb : PInt p b) : PInt p (a + b) := by
  obtain ⟨u₁, v₁, h₁, e₁⟩ := ha
  obtain ⟨u₂, v₂, h₂, e₂⟩ := hb
  refine ⟨u₁ * v₂ + u₂ * v₁, v₁ * v₂, Nat.Coprime.mul_right h₁ h₂, ?_⟩
  push_cast
  rw [← e₁, ← e₂]; ring

theorem PInt.neg {p : ℕ} {a : ℚ} (ha : PInt p a) : PInt p (-a) := by
  obtain ⟨u, v, h, e⟩ := ha
  exact ⟨-u, v, h, by push_cast; rw [← e]; ring⟩

theorem PInt.sum {p : ℕ} {ι : Type*} (S : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ S, PInt p (f i)) :
    PInt p (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PInt.int p 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Adding a `p`-integral number does not change `p`-integrality. -/
theorem PInt.add_iff {p : ℕ} {a b : ℚ} (hb : PInt p b) : PInt p (a + b) ↔ PInt p a := by
  constructor
  · intro h; simpa using h.add hb.neg
  · intro h; exact h.add hb

/-- `p^j / n'` is `p`-integral when `p ∤ n'`. -/
theorem PInt.pow_div {p j n' : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n') (hn0 : 0 < n') :
    PInt p ((p : ℚ) ^ j / n') :=
  ⟨p ^ j, n', (Nat.Prime.coprime_iff_not_dvd hp).2 hn, by
    push_cast; field_simp⟩

/-- A term `p^(s-1)/n` with `p^s ∤ n` is `p`-integral. -/
theorem PInt.term_of_not_dvd {p s n : ℕ} (hp : p.Prime) (hn0 : 0 < n) (hns : ¬ p ^ s ∣ n) :
    PInt p ((p : ℚ) ^ (s - 1) * (1 / n)) := by
  set j := n.factorization p
  have hjs : j < s := by
    by_contra h
    exact hns ((Nat.pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd n p))
  set n' := n / p ^ j
  have hn : p ^ j * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hn' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hp (by omega)
  have hn'0 : 0 < n' := Nat.pos_of_ne_zero (by rintro h; rw [h] at hn; omega)
  have key : (p : ℚ) ^ (s - 1) * (1 / n) = (p : ℚ) ^ (s - 1 - j) / n' := by
    rw [← hn]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (p : ℚ) ^ (s - 1) = p ^ (s - 1 - j) * p ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [this]; push_cast
    field_simp
  rw [key]
  exact PInt.pow_div hp hn' hn'0

/-! ## 2.  The row lemma: full prime-power precision -/

/-- **Row lemma.**  With `J = p^r J'`, `p ∤ J'`, an integer `S` satisfies
`S / (p J)` is `p`-integral **iff** `p^(r+1) ∣ S`. -/
theorem row_pint_iff {p r J' : ℕ} (hp : p.Prime) (hJ' : ¬ p ∣ J') (hJ'0 : 0 < J') (S : ℤ) :
    PInt p ((S : ℚ) / (p * (p ^ r * J'))) ↔ ((p : ℤ) ^ (r + 1)) ∣ S := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hJ0 : (J' : ℚ) ≠ 0 := by exact_mod_cast hJ'0.ne'
  constructor
  · rintro ⟨u, v, hv, e⟩
    have hcop : IsCoprime ((p : ℤ) ^ (r + 1)) (v : ℤ) := by
      have := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left (r + 1) hv)
      simpa using this
    apply hcop.dvd_of_dvd_mul_right
    refine ⟨u * J', ?_⟩
    have : (S : ℚ) * v = u * (p * (p ^ r * J')) := by
      field_simp at e; linarith
    have : ((S * v : ℤ) : ℚ) = ((p ^ (r + 1) * (u * J') : ℤ) : ℚ) := by
      push_cast; rw [this]; ring
    exact_mod_cast this
  · rintro ⟨S', rfl⟩
    refine ⟨S', J', (Nat.Prime.coprime_iff_not_dvd hp).2 hJ', ?_⟩
    push_cast
    field_simp
    ring

/-! ## 3.  Owner data and the full row congruence -/

/-- The row set of owner `Q` on `I` for the word `x`: cofactors `c ∈ [1, ⌊M/Q⌋]` with
`Q c ∈ I` selected. -/
def rowSet (I : Finset ℕ) (x : ℕ → Bool) (M Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (M / Q)).filter fun c => Q * c ∈ I ∧ x (Q * c) = true

/-- The row sum `∑_{Q c ∈ I} x_{Qc} (J / c)` with `J = L_{⌊M/Q⌋}`. -/
def rowSum (I : Finset ℕ) (x : ℕ → Bool) (M Q : ℕ) : ℤ :=
  ∑ c ∈ rowSet I x M Q, ((lcmUpTo (M / Q) / c : ℕ) : ℤ)

/-- The full row congruence modulo `d_p = p^(r_p+1)`. -/
def RowCongruence (I : Finset ℕ) (x : ℕ → Bool) (M p s r : ℕ) : Prop :=
  ((p : ℤ) ^ (r + 1)) ∣ rowSum I x M (p ^ s)

/-- The `p`-local denominator-entry condition at scale `p^(s-1)` (`= p^{v_p(L_T)}`). -/
def PLocalEntry (I : Finset ℕ) (x : ℕ → Bool) (p s : ℕ) : Prop :=
  PInt p ((p : ℚ) ^ (s - 1) * ∑ n ∈ selected I x, (1 : ℚ) / n)

/-- `r_p = v_p(J_p)` gives the required decomposition `J_p = p^{r_p} J'` with `p ∤ J'`. -/
theorem lcm_decomp {p m : ℕ} (hp : p.Prime) :
    lcmUpTo m = p ^ (lcmUpTo m).factorization p * (lcmUpTo m / p ^ (lcmUpTo m).factorization p)
      ∧ ¬ p ∣ lcmUpTo m / p ^ (lcmUpTo m).factorization p :=
  ⟨(Nat.ordProj_mul_ordCompl_eq_self _ p).symm, Nat.not_dvd_ordCompl hp (lcmUpTo_ne_zero m)⟩

/-- The `Q`-multiples among the selected points are exactly `Q · rowSet`. -/
theorem image_rowSet {I : Finset ℕ} {x : ℕ → Bool} {M Q : ℕ} (hQ : 0 < Q)
    (hI : ∀ n ∈ I, 1 ≤ n ∧ n ≤ M) :
    (rowSet I x M Q).image (fun c => Q * c) = (selected I x).filter fun n => Q ∣ n := by
  ext n
  simp only [rowSet, selected, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨c, ⟨⟨-, -⟩, hcI, hcx⟩, rfl⟩
    exact ⟨⟨hcI, hcx⟩, dvd_mul_right _ _⟩
  · rintro ⟨⟨hnI, hnx⟩, c, rfl⟩
    have h := hI _ hnI
    refine ⟨c, ⟨⟨?_, ?_⟩, hnI, hnx⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at h
      · exact h0
    · rw [Nat.le_div_iff_mul_le hQ]; linarith [h.2]

/-- **The exact ENTRY equivalence for one owner.**  For `p` prime, `s ≥ 1`, `Q = p^s`, a finite
`I ⊆ [1, M]`, any word `x`, and `J_p = p^r J'` with `p ∤ J'` (i.e. `r = r_p = v_p(J_p)`):
the `p`-local denominator-entry condition holds iff the full row congruence modulo
`p^(r+1)` holds. -/
theorem pLocal_entry_iff_row_congruence {I : Finset ℕ} {x : ℕ → Bool} {M p s r J' : ℕ}
    (hp : p.Prime) (hs : 1 ≤ s) (hI : ∀ n ∈ I, 1 ≤ n ∧ n ≤ M)
    (hJ : lcmUpTo (M / p ^ s) = p ^ r * J') (hJ' : ¬ p ∣ J') :
    PLocalEntry I x p s ↔ RowCongruence I x M p s r := by
  have hQ : 0 < p ^ s := pow_pos hp.pos s
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hJ'0 : 0 < J' := by
    rcases Nat.eq_zero_or_pos J' with h | h
    · exfalso; rw [h, mul_zero] at hJ; exact lcmUpTo_ne_zero _ hJ
    · exact h
  unfold PLocalEntry RowCongruence
  -- split the selected sum into `Q`-multiples and the rest
  rw [← Finset.sum_filter_add_sum_filter_not (selected I x) (fun n => p ^ s ∣ n), mul_add]
  have hrest : PInt p ((p : ℚ) ^ (s - 1) *
      ∑ n ∈ (selected I x).filter (fun n => ¬ p ^ s ∣ n), (1 : ℚ) / n) := by
    rw [Finset.mul_sum]
    refine PInt.sum _ _ fun n hn => ?_
    simp only [Finset.mem_filter, selected] at hn
    exact PInt.term_of_not_dvd hp (hI n hn.1.1).1 hn.2
  rw [PInt.add_iff hrest, ← image_rowSet hQ hI, Finset.sum_image
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hQ h)]
  -- identify the row part with `rowSum / (p J)`
  have hrow : (p : ℚ) ^ (s - 1) * ∑ c ∈ rowSet I x M (p ^ s), (1 : ℚ) / ((p ^ s * c : ℕ) : ℚ)
      = (rowSum I x M (p ^ s) : ℚ) / (p * (p ^ r * J')) := by
    unfold rowSum
    rw [Finset.mul_sum, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [rowSet, Finset.mem_filter, Finset.mem_Icc] at hc
    have hcJ : c ∣ lcmUpTo (M / p ^ s) := dvd_lcmUpTo hc.1.1 hc.1.2
    have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
    rw [Int.cast_natCast, Nat.cast_div hcJ hc0, hJ]
    have hps : (p : ℚ) ^ s = p ^ (s - 1) * p := by rw [← pow_succ]; congr 1; omega
    push_cast
    rw [hps]
    have : (J' : ℚ) ≠ 0 := by exact_mod_cast hJ'0.ne'
    field_simp
  rw [hrow]
  exact row_pint_iff hp hJ' hJ'0 _

/-! ## 4.  Firewall: the top digit alone is insufficient -/

/-- **Top digit only is insufficient.**  At `p = 2`, `s = 2` (`Q = 4`, first power above
`T = 3`), `M = 12`, `I = {4}`, all bits `1`: `J = L_3 = 6 = 2¹·3` (`r = 1`, `d = 4`), the row sum
is `6`, which passes the mod-`p` test but fails the full mod-`p^(r+1)` test; accordingly the
`2`-local entry condition fails (`2 · 1/4 = 1/2`). -/
theorem top_digit_insufficient :
    lcmUpTo (12 / 2 ^ 2) = 2 ^ 1 * 3 ∧
    rowSum {4} (fun _ => true) 12 (2 ^ 2) = 6 ∧
    (2 : ℤ) ∣ rowSum {4} (fun _ => true) 12 (2 ^ 2) ∧
    ¬ RowCongruence {4} (fun _ => true) 12 2 2 1 ∧
    ¬ PLocalEntry {4} (fun _ => true) 2 2 := by
  have hL : lcmUpTo (12 / 2 ^ 2) = 2 ^ 1 * 3 := by decide
  have hR : rowSum {4} (fun _ => true) 12 (2 ^ 2) = 6 := by
    unfold rowSum rowSet
    rw [show 12 / 2 ^ 2 = 3 by norm_num, show lcmUpTo 3 = 6 by decide]
    decide
  have hRC : ¬ RowCongruence {4} (fun _ => true) 12 2 2 1 := by
    unfold RowCongruence; rw [hR]; decide
  refine ⟨hL, hR, by rw [hR]; decide, hRC, ?_⟩
  rw [pLocal_entry_iff_row_congruence Nat.prime_two (by norm_num)
    (by intro n hn; simp at hn; omega) hL (by decide)]
  exact hRC

/-- The mod-`p` shadow of the row congruence does not imply the full congruence. -/
theorem mod_p_not_sufficient :
    ¬ ∀ (I : Finset ℕ) (x : ℕ → Bool) (M p s r : ℕ),
      (p : ℤ) ∣ rowSum I x M (p ^ s) → RowCongruence I x M p s r := by
  intro h
  obtain ⟨-, -, h2, h4, -⟩ := top_digit_insufficient
  exact h4 (h {4} (fun _ => true) 12 2 2 1 (by exact_mod_cast h2))

end ExactEntrySystem
end ResearchBankV8
end Erdos287
