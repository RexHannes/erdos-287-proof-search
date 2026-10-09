import RequestProject.Erdos287.PostV64V71.SourceRows

/-!
# Erdős #287 — V68/V69 exceptional primes `E_H(M)` and residual denominator `D₂(M)`

**Status: BANK (LEAN PROVED)** for the exact divisibility statements.  The analytic size
estimates (`log Ξ_H < 2M/L⁵`, `log D₂ < 0.872 M / log M`) are **not** proved here; they are
recorded as named propositions in `TailClosure.lean` / `CurrentLedger.lean`.

Convention: `y = ⌊M/H⌋` (natural floor).  For a natural `q`, `q > ⌊M/H⌋ ↔ q > M/H`.

* `exceptionalPrimes M H = {q prime : ⌊M/H⌋ < q ≤ M, q ∣ Ξ_H}` (`E_H(M)`);
* `prod_exceptionalPrimes_dvd_Xi` — `∏_{q∈E_H} q ∣ Ξ_H`;
* `BE M H = ∑_{q∈E_H} log q` and `BE_le_log_Xi` — `B_E ≤ log Ξ_H`;
* `Dlo y M = ∏_{p ≤ y prime} p^{⌊log_p M⌋}`, `D2 M H = Dlo ⌊M/H⌋ M · ∏_{q∈E_H} q`;
* `selected_dvd_D2` — every denominator of a hypothetical counterexample divides `D₂(M)`,
  provided `M < (⌊M/H⌋ + 1)²` (every prime `> M/H` divides each `n ≤ M` at most once).
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

/-- `E_H(M)`: the exceptional primes `q ∈ (M/H, M]` dividing `Ξ_H`. -/
def exceptionalPrimes (M H : ℕ) : Finset ℕ :=
  (Finset.Ioc (M / H) M).filter (fun q => q.Prime ∧ q ∣ Xi H)

theorem mem_exceptionalPrimes {M H q : ℕ} :
    q ∈ exceptionalPrimes M H ↔ (M / H < q ∧ q ≤ M) ∧ q.Prime ∧ q ∣ Xi H := by
  simp [exceptionalPrimes]

/-- `∏_{q∈E_H} q ∣ Ξ_H`. -/
theorem prod_exceptionalPrimes_dvd_Xi (M H : ℕ) : (∏ q ∈ exceptionalPrimes M H, q) ∣ Xi H := by
  refine Finset.prod_primes_dvd _ (fun q hq => ?_) (fun q hq => ?_)
  · exact (mem_exceptionalPrimes.1 hq).2.1.prime
  · exact (mem_exceptionalPrimes.1 hq).2.2

/-- The exceptional log budget `B_E = ∑_{q∈E_H} log q`. -/
noncomputable def BE (M H : ℕ) : ℝ := ∑ q ∈ exceptionalPrimes M H, Real.log q

theorem BE_nonneg (M H : ℕ) : 0 ≤ BE M H :=
  Finset.sum_nonneg fun q _ => Real.log_natCast_nonneg q

/-- `B_E ≤ log Ξ_H`. -/
theorem BE_le_log_Xi (M H : ℕ) : BE M H ≤ Real.log (Xi H) := by
  have hpos : ∀ q ∈ exceptionalPrimes M H, (q : ℝ) ≠ 0 := fun q hq => by
    have := (mem_exceptionalPrimes.1 hq).2.1.pos; positivity
  have hle : (∏ q ∈ exceptionalPrimes M H, q) ≤ Xi H :=
    Nat.le_of_dvd (Xi_pos H) (prod_exceptionalPrimes_dvd_Xi M H)
  have hprodpos : 0 < (∏ q ∈ exceptionalPrimes M H, (q : ℝ)) :=
    Finset.prod_pos fun q hq => by have := (mem_exceptionalPrimes.1 hq).2.1.pos; positivity
  unfold BE
  rw [← Real.log_prod hpos]
  apply Real.log_le_log hprodpos
  have : ((∏ q ∈ exceptionalPrimes M H, q : ℕ) : ℝ) ≤ (Xi H : ℝ) := by exact_mod_cast hle
  simpa using this

/-- `D_lo(y, M) = ∏_{p ≤ y prime} p^{⌊log_p M⌋}` (all required maximal powers of base primes). -/
def Dlo (y M : ℕ) : ℕ := ∏ p ∈ (Finset.Icc 1 y).filter Nat.Prime, p ^ Nat.log p M

/-- The V68/V69 residual denominator `D₂(M) = D_lo · ∏_{q ∈ E_H(M)} q`. -/
def D2 (M H : ℕ) : ℕ := Dlo (M / H) M * ∏ q ∈ exceptionalPrimes M H, q

/-- `M < (⌊M/H⌋+1)·q` whenever `q > ⌊M/H⌋`. -/
theorem lt_mul_of_div_lt {M H q : ℕ} (hH : 0 < H) (hq : M / H < q) : M < q * H := by
  have := Nat.lt_mul_div_succ M hH
  have h2 : M / H + 1 ≤ q := hq
  calc M < H * (M / H + 1) := this
    _ ≤ H * q := Nat.mul_le_mul_left _ h2
    _ = q * H := mul_comm _ _

namespace Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- **Selected denominators divide `D₂(M)`.**  Assume `H ≥ 1` and `M < (⌊M/H⌋ + 1)²`.  Then
every `n ∈ A` divides `D₂(M)`. -/
theorem selected_dvd_D2 {H : ℕ} (hH : 0 < H) (hy : ce.M < (ce.M / H + 1) ^ 2) :
    ∀ n ∈ ce.A, n ∣ D2 ce.M H := by
  intro n hn
  have hn0 : 0 < n := ce.hpos n hn
  have hnM : n ≤ ce.M := (le_M ce) hn
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpkle : p ^ k ≤ ce.M := le_trans (Nat.le_of_dvd hn0 hpk) hnM
  by_cases hpy : p ≤ ce.M / H
  · -- small prime: `p^k ∣ p^{⌊log_p M⌋} ∣ D_lo`
    have hklog : k ≤ Nat.log p ce.M :=
      Nat.le_log_of_pow_le hp.one_lt hpkle
    have h1 : p ^ k ∣ p ^ Nat.log p ce.M := pow_dvd_pow p hklog
    have h2 : p ^ Nat.log p ce.M ∣ Dlo (ce.M / H) ce.M := by
      unfold Dlo
      apply Finset.dvd_prod_of_mem
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.one_lt.le, hpy⟩, hp⟩
    exact dvd_trans (dvd_trans h1 h2) (dvd_mul_right _ _)
  · -- large prime: `k = 1` and `p ∈ E_H`
    push_neg at hpy
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by omega
      have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
      have h3 : (ce.M / H + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hpy 2
      omega
    subst hk1
    rw [pow_one] at hpk ⊢
    have hpM : p ≤ ce.M := le_trans (Nat.le_of_dvd hn0 hpk) hnM
    have hpXi : p ∣ Xi H := by
      by_contra hc
      exact (all_good_multiples_omitted ce) hp (lt_mul_of_div_lt hH hpy) hc hpk hn
    have hpE : p ∈ exceptionalPrimes ce.M H := mem_exceptionalPrimes.2 ⟨⟨hpy, hpM⟩, hp, hpXi⟩
    exact dvd_trans (Finset.dvd_prod_of_mem _ hpE) (dvd_mul_left _ _)

end Gap2CE

end Erdos287.PostV64V71
