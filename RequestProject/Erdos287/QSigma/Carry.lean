import RequestProject.Erdos287.QSigma.Source

/-!
# Erdős #287 — the full `p`-adic carry system and `Q_Σ`

For a prime `p` with `p^e ‖ W` and a depth `1 ≤ d ≤ e`:

* `S_{p,d} = { n ∈ V : p^(e-d+1) ∣ n }`;
* `κ_{p,d}` is the least size of a set `F ⊆ S_{p,d}` with `∑_{n∈F} W/n ≡ T (mod p^d)`;
* `Γ_p = ∑_{d=1}^{e} κ_{p,d}` and `Q_Σ = ∏_{p ∣ W} p^{Γ_p}`.

`κ_{p,d}` is defined as an `sInf` of a set of natural numbers.  If the set is empty
(the depth is *infeasible*) the junk value is `0`; this never affects soundness because
`no_solution_of_infeasible` shows that an infeasible depth already kills the source, and
whenever a solution exists every depth set is nonempty, so `κ_{p,d}` is the true minimum.

Main results:

* `kappa_le_card_inter` — every solution uses at least `κ_{p,d}` elements of `S_{p,d}`;
* `Gamma_le_factorization_prod` — `v_p(∏_{n∈E} n) ≥ ∑_d κ_{p,d}` (sum of depths, not max);
* `QSigma_dvd_prod` — **(DIV)** `Q_Σ ∣ ∏_{n∈E} n`.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-- The exponent `e` with `p^e ‖ W`. -/
def eW (a M : ℕ) (R : Finset ℕ) (p : ℕ) : ℕ := (W a M R).factorization p

/-- The depth set `S_{p,d} = { n ∈ V : p^(e-d+1) ∣ n }`. -/
def S (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : Finset ℕ :=
  (V a M R).filter (fun n => p ^ (eW a M R p - d + 1) ∣ n)

/-- The sizes of all repair sets at depth `d`. -/
def RepairSizes (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : Set ℕ :=
  {k | ∃ F ⊆ S a M R p d, F.card = k ∧
    (∑ n ∈ F, ((W a M R / n : ℕ) : ℤ)) ≡ T a M R [ZMOD (p : ℤ) ^ d]}

/-- The exact minimum repair multiplicity `κ_{p,d}` (junk value `0` if infeasible). -/
noncomputable def kappa (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : ℕ := sInf (RepairSizes a M R p d)

/-- `Γ_p = ∑_{d=1}^{e} κ_{p,d}` (the sum-of-depths certificate). -/
noncomputable def Gamma (a M : ℕ) (R : Finset ℕ) (p : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 (eW a M R p), kappa a M R p d

/-- `Q_Σ = ∏_{p^e ‖ W} p^{Γ_p}`. -/
noncomputable def QSigma (a M : ℕ) (R : Finset ℕ) : ℕ :=
  ∏ p ∈ (W a M R).primeFactors, p ^ Gamma a M R p

/-- Elements of `V` outside `S_{p,d}` contribute `W/n ≡ 0 (mod p^d)`. -/
lemma pow_dvd_W_div_of_not_mem_S (ha : 0 < a) {p d n : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) (hn : n ∈ V a M R) (hnS : ¬ p ^ (eW a M R p - d + 1) ∣ n) :
    p ^ d ∣ W a M R / n := by
  have hB := V_subset_B hn
  have hnW := dvd_W_of_mem_B hB
  have hnpos : 0 < n := pos_of_mem_B ha hB
  have hW0 : W a M R ≠ 0 := W_ne_zero ha
  have hq0 : W a M R / n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hnW) hnpos).ne'
  rw [hp.pow_dvd_iff_le_factorization hq0, Nat.factorization_div hnW]
  rw [hp.pow_dvd_iff_le_factorization hnpos.ne'] at hnS
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  unfold eW at hd hnS
  omega

/-- **Carry lemma.**  The part of a solution lying in `S_{p,d}` is a repair set. -/
theorem card_inter_mem_RepairSizes (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E)
    {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p) :
    (E.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n)).card ∈ RepairSizes a M R p d := by
  refine ⟨E.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n), ?_, rfl, ?_⟩
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_filter.2 ⟨h.1 hn.1, hn.2⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not E
      (fun n => p ^ (eW a M R p - d + 1) ∣ n) (fun n => ((W a M R / n : ℕ) : ℤ))
    have hrest : ((p : ℤ) ^ d) ∣ ∑ n ∈ E.filter (fun n => ¬ p ^ (eW a M R p - d + 1) ∣ n),
        ((W a M R / n : ℕ) : ℤ) := by
      refine Finset.dvd_sum (fun n hn => ?_)
      rw [Finset.mem_filter] at hn
      have := pow_dvd_W_div_of_not_mem_S ha hp hd (h.1 hn.1) hn.2
      exact_mod_cast this
    rw [← h.2.2, ← hsplit, Int.modEq_iff_dvd]
    simpa using hrest

/-- Every solution uses at least `κ_{p,d}` elements of `S_{p,d}`. -/
theorem kappa_le_card_inter (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E)
    {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p) :
    kappa a M R p d ≤ (E.filter (fun n => p ^ (eW a M R p - d + 1) ∣ n)).card :=
  Nat.sInf_le (card_inter_mem_RepairSizes ha h hp hd)

/-- If some depth `1 ≤ d ≤ e` is infeasible (`κ_{p,d} = ∞`), the source has no solution. -/
theorem no_solution_of_infeasible (ha : 0 < a) {p d : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) (hinf : RepairSizes a M R p d = ∅) (E : Finset ℕ) :
    ¬ SourceSol a M R E := by
  intro h
  have := card_inter_mem_RepairSizes ha h hp hd
  rw [hinf] at this
  exact this

/-- Valuation as a count of depths: for `v_p(n) ≤ e`,
`v_p(n) = #{d ∈ [1,e] : p^(e-d+1) ∣ n}`. -/
lemma factorization_eq_card_depths {p n e : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (he : n.factorization p ≤ e) :
    n.factorization p = ((Finset.Icc 1 e).filter (fun d => p ^ (e - d + 1) ∣ n)).card := by
  have : (Finset.Icc 1 e).filter (fun d => p ^ (e - d + 1) ∣ n) =
      Finset.Icc (e + 1 - n.factorization p) e := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, hp.pow_dvd_iff_le_factorization hn]
    omega
  rw [this, Nat.card_Icc]
  omega

/-- **Sum-of-depths valuation bound.**  For every solution and every prime `p`,
`v_p(∏_{n∈E} n) ≥ Γ_p = ∑_{d=1}^{e} κ_{p,d}`. -/
theorem Gamma_le_factorization_prod (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E)
    {p : ℕ} (hp : p.Prime) :
    Gamma a M R p ≤ (∏ n ∈ E, n).factorization p := by
  have hE0 : ∀ n ∈ E, n ≠ 0 := fun n hn => (pos_of_mem_B ha (V_subset_B (h.1 hn))).ne'
  rw [Nat.factorization_prod hE0, Finsupp.coe_finset_sum, Finset.sum_apply]
  have hval : ∀ n ∈ E, n.factorization p =
      ((Finset.Icc 1 (eW a M R p)).filter (fun d => p ^ (eW a M R p - d + 1) ∣ n)).card := by
    intro n hn
    apply factorization_eq_card_depths hp (hE0 n hn)
    have hnW := dvd_W_of_mem_B (V_subset_B (h.1 hn))
    exact (Nat.factorization_le_iff_dvd (hE0 n hn) (W_ne_zero ha)).2 hnW p
  rw [Finset.sum_congr rfl hval]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  unfold Gamma
  refine Finset.sum_le_sum (fun d hd => ?_)
  have hd' : d ≤ eW a M R p := (Finset.mem_Icc.1 hd).2
  have := kappa_le_card_inter ha h hp hd'
  rw [Finset.card_filter] at this
  exact this

/-- **(DIV)**  For every solution `E` of the exact source, `Q_Σ ∣ ∏_{n∈E} n`. -/
theorem QSigma_dvd_prod (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    QSigma a M R ∣ ∏ n ∈ E, n := by
  have hE0 : ∀ n ∈ E, n ≠ 0 := fun n hn => (pos_of_mem_B ha (V_subset_B (h.1 hn))).ne'
  have hP0 : (∏ n ∈ E, n) ≠ 0 := Finset.prod_ne_zero_iff.2 hE0
  have hQ0 : QSigma a M R ≠ 0 := by
    unfold QSigma
    refine Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ ?_)
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Nat.factorization_prime_le_iff_dvd hQ0 hP0]
  intro q hq
  have hfac : (QSigma a M R).factorization q ≤ Gamma a M R q := by
    unfold QSigma
    rw [Nat.factorization_prod (fun p hp => pow_ne_zero _
      (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    rw [Finsupp.coe_finset_sum, Finset.sum_apply]
    simp_rw [Nat.factorization_pow]
    by_cases hqW : q ∈ (W a M R).primeFactors
    · rw [Finset.sum_eq_single q]
      · simp [hq.factorization_self]
      · intro p hp hpq
        have hp' := Nat.prime_of_mem_primeFactors hp
        simp [hp'.factorization, hpq]
      · intro h'; exact absurd hqW h'
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        have hpq : p ≠ q := fun e => hqW (e ▸ hp)
        simp [hp'.factorization, hpq]
  exact hfac.trans (Gamma_le_factorization_prod ha h hq)

end Erdos287.ExactSource
