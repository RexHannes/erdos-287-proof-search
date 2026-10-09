import RequestProject.Erdos287.QSigma.Certificate

/-!
# Erdős #287 — hostile-audit bounds on both sides of `Q_Σ > P_max`

These bounds say how strong the certificate can possibly be.  They are not closure
results.

* `QSigma_factorization` — `v_q(Q_Σ) = Γ_q` for `q ∣ W`.
* `denominator_dvd_QSigma` — **floor**: if a solution exists, then
  `W / gcd(W, |T|) ∣ Q_Σ`.  So `Q_Σ` is never weaker than the trivial denominator
  certificate, because every depth `d > v_p(T)` costs at least one repair.
* `QSigma_dvd_prod_V` — **ceiling**: `Q_Σ ∣ ∏_{n∈V} n` holds unconditionally, so
  `log Q_Σ ≤ ∑_{n∈V} log n`.
* `Pmax_le_pow` and `pow_le_Pmass` — the comparator lies between `a^{|F|}` (for any
  admissible `F`) and `M^{R_T}`.  So the mass-sharpened product bound improves on the
  crude bound by at most a factor `log M / log a` in logarithmic scale.
-/

open scoped BigOperators

namespace Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-- `v_q(Q_Σ) = Γ_q` for every prime factor `q` of `W`. -/
theorem QSigma_factorization {q : ℕ} (hq : q ∈ (W a M R).primeFactors) :
    (QSigma a M R).factorization q = Gamma a M R q := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  unfold QSigma
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp_rw [Nat.factorization_pow]
  rw [Finset.sum_eq_single q]
  · simp [hqp.factorization_self]
  · intro p hp hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    simp [hp'.factorization, hpq]
  · intro h'; exact absurd hq h'

lemma QSigma_ne_zero : QSigma a M R ≠ 0 := by
  unfold QSigma
  refine Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ ?_)
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- `v_q(Q_Σ) = 0` for primes `q ∤ W`. -/
theorem QSigma_factorization_of_not_mem {q : ℕ} (hq : q ∉ (W a M R).primeFactors) :
    (QSigma a M R).factorization q = 0 := by
  unfold QSigma
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  simp_rw [Nat.factorization_pow]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpq : p ≠ q := fun e => hq (e ▸ hp)
  simp [hp'.factorization, hpq]

/-- A depth `d` with `p^d ∤ T` costs at least one repair, whenever a solution exists. -/
theorem one_le_kappa (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) {p d : ℕ}
    (hp : p.Prime) (hd : d ≤ eW a M R p) (hT : ¬ ((p : ℤ) ^ d ∣ T a M R)) :
    1 ≤ kappa a M R p d := by
  have hne : (RepairSizes a M R p d).Nonempty := ⟨_, card_inter_mem_RepairSizes ha h hp hd⟩
  have hmem := Nat.sInf_mem hne
  rcases Nat.eq_zero_or_pos (kappa a M R p d) with h0 | h0
  · exfalso
    unfold kappa at h0
    rw [h0] at hmem
    obtain ⟨F, -, hF0, hFmod⟩ := hmem
    rw [Finset.card_eq_zero] at hF0
    subst hF0
    simp only [Finset.sum_empty] at hFmod
    exact hT (Int.modEq_zero_iff_dvd.1 hFmod.symm)
  · exact h0

/-- **Floor.**  If a solution exists then `W / gcd(W, |T|) ∣ Q_Σ`. -/
theorem denominator_dvd_QSigma (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    W a M R / Nat.gcd (W a M R) (T a M R).natAbs ∣ QSigma a M R := by
  have hW0 : W a M R ≠ 0 := W_ne_zero ha
  set g := Nat.gcd (W a M R) (T a M R).natAbs with hg
  have hgW : g ∣ W a M R := Nat.gcd_dvd_left _ _
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hW0)).ne'
  have hq0 : W a M R / g ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hgW) (Nat.pos_of_ne_zero hg0)).ne'
  rw [← Nat.factorization_prime_le_iff_dvd hq0 QSigma_ne_zero]
  intro q hq
  rw [Nat.factorization_div hgW]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  by_cases hqW : q ∈ (W a M R).primeFactors
  · rw [QSigma_factorization hqW]
    by_cases hT0 : T a M R = 0
    · have : g = W a M R := by rw [hg, hT0]; simp
      rw [this]; simp
    · have hTn : (T a M R).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hT0
      rw [hg, Nat.factorization_gcd hW0 hTn]
      simp only [Finsupp.inf_apply]
      set e := (W a M R).factorization q with he
      set v := (T a M R).natAbs.factorization q with hv
      -- every depth `d ∈ (v, e]` costs at least one repair
      have hcount : ((Finset.Icc 1 e).filter (fun d => v < d)).card ≤ Gamma a M R q := by
        unfold Gamma
        rw [Finset.card_filter]
        refine Finset.sum_le_sum (fun d hd => ?_)
        split_ifs with hvd
        · apply one_le_kappa ha h hq (Finset.mem_Icc.1 hd).2
          intro hdvd
          have : q ^ d ∣ (T a M R).natAbs := by
            have := Int.natAbs_dvd_natAbs.2 hdvd
            simpa [Int.natAbs_pow] using this
          rw [hq.pow_dvd_iff_le_factorization hTn] at this
          omega
        · exact Nat.zero_le _
      have hset : (Finset.Icc 1 e).filter (fun d => v < d) = Finset.Icc (v + 1) e := by
        ext d; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hset, Nat.card_Icc] at hcount
      have : e - min e v = e + 1 - (v + 1) := by omega
      rw [this]
      exact hcount
  · have : (W a M R).factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      right; left
      intro hdvd
      exact hqW (Nat.mem_primeFactors.2 ⟨hq, hdvd, hW0⟩)
    rw [this]; simp

/-- `κ_{p,d} ≤ |S_{p,d}|` (unconditionally; the junk value `0` also satisfies it). -/
theorem kappa_le_card_S (p d : ℕ) : kappa a M R p d ≤ (S a M R p d).card := by
  rcases (RepairSizes a M R p d).eq_empty_or_nonempty with he | hne
  · unfold kappa; rw [he, Nat.sInf_empty]; exact Nat.zero_le _
  · obtain ⟨F, hFS, hFc, -⟩ := Nat.sInf_mem hne
    unfold kappa
    rw [← hFc]
    exact Finset.card_le_card hFS

/-- **Ceiling.**  `Q_Σ ∣ ∏_{n∈V} n`, so `log Q_Σ ≤ ∑_{n∈V} log n`. -/
theorem QSigma_dvd_prod_V (ha : 0 < a) : QSigma a M R ∣ ∏ n ∈ V a M R, n := by
  have hV0 : ∀ n ∈ V a M R, n ≠ 0 := fun n hn => (pos_of_mem_B ha (V_subset_B hn)).ne'
  have hP0 : (∏ n ∈ V a M R, n) ≠ 0 := Finset.prod_ne_zero_iff.2 hV0
  rw [← Nat.factorization_prime_le_iff_dvd QSigma_ne_zero hP0]
  intro q hq
  by_cases hqW : q ∈ (W a M R).primeFactors
  · rw [QSigma_factorization hqW, Nat.factorization_prod hV0, Finsupp.coe_finset_sum,
      Finset.sum_apply]
    have hval : ∀ n ∈ V a M R, n.factorization q =
        ((Finset.Icc 1 (eW a M R q)).filter (fun d => q ^ (eW a M R q - d + 1) ∣ n)).card := by
      intro n hn
      apply factorization_eq_card_depths hq (hV0 n hn)
      exact (Nat.factorization_le_iff_dvd (hV0 n hn) (W_ne_zero ha)).2
        (dvd_W_of_mem_B (V_subset_B hn)) q
    rw [Finset.sum_congr rfl hval]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    unfold Gamma
    refine Finset.sum_le_sum (fun d _ => ?_)
    have := kappa_le_card_S (a := a) (M := M) (R := R) q d
    rw [S, Finset.card_filter] at this
    exact this
  · rw [QSigma_factorization_of_not_mem hqW]; exact Nat.zero_le _

/-- Upper end of the comparator: `P_max(V, k) ≤ M^k` (for `M > 0`). -/
theorem Pmax_le_pow (hM : 0 < M) (k : ℕ) : Pmax a M R k ≤ M ^ k := by
  classical
  unfold Pmax
  refine Finset.sup_le (fun F hF => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hF
  calc (∏ n ∈ F, n) ≤ ∏ _n ∈ F, M :=
        Finset.prod_le_prod' (fun n hn => (mem_B.1 (V_subset_B (hF.1 hn))).2.1)
    _ = M ^ F.card := Finset.prod_const M
    _ ≤ M ^ k := Nat.pow_le_pow_right hM hF.2.2

/-- Lower end of the comparator: for every independent `F ⊆ V` with `∑_{n∈F} 1/n ≤ τ`,
`a^{|F|} ≤ P_mass`. -/
theorem pow_le_Pmass {F : Finset ℕ} (hF : F ⊆ V a M R) (hind : Indep F)
    (hm : (∑ n ∈ F, (1 : ℚ) / n) ≤ tau a M R) : a ^ F.card ≤ Pmass a M R := by
  classical
  calc a ^ F.card = ∏ _n ∈ F, a := (Finset.prod_const a).symm
    _ ≤ ∏ n ∈ F, n := Finset.prod_le_prod' (fun n hn => (mem_B.1 (V_subset_B (hF hn))).1)
    _ ≤ Pmass a M R := by
        unfold Pmass
        refine Finset.le_sup (f := fun F => ∏ n ∈ F, n) ?_
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hF, hind, hm⟩

end Erdos287.ExactSource
