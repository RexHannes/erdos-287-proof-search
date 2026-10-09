import RequestProject.Erdos287.SourceChain.Physical.TypeII.ScopedProviders

/-!
# Erdős #287 — `OrdinaryBVUremProviderScoped` is FALSE (formal counterexample)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

`not_ordinaryBVUremProviderScoped` proves `¬ OrdinaryBVUremProviderScoped κ` for every
`κ ∈ (0, 10⁻⁵)` (the whole critical regime).  Two independent defects of the statement are used:

1. **Vacuous distribution hypothesis.**  The Siegel–Walfisz parameters `A'`, `B` are universally
   quantified *by the caller*; with `B = 0` the condition `SWSeqMasked α N A' 0 _` only tests
   `q = 1`, where the difference is identically `0`.  So the "distribution hypothesis" is no
   hypothesis at all.
2. **Moduli sharing a prime with the affine residue.**  Nothing forces `(l, A·B) = 1`.  With
   `A = 1`, `B = 3`, `f = 2`, `K = 4`, the low modulus `l = 3` survives (`ℓ_X(3) = -1`,
   `ellX_three`), and on odd multiples `v` of `3` one has `h_3(v) = I_3(v) - U_3(v) = 1 - 0`:
   no cancellation at all (`weight_eq_one`).

With `X = 2^{6r}`, `N = 2^i` a prime-rich dyadic block (`exists_prime_block`, from the elementary
Chebyshev bound `two_pow_le_primes`), `M = 2^{6r-i-1}`, `α = 1_{primes in [N,2N)}`,
`β = 1_{m ∈ [M,2M), m ≡ 3 (6)}`, the `h_l U_r` part is exactly
`-π[N,2N) · #{m ∈ [M,2M) : m ≡ 3 (6)}` (`physUrem_eq_three`, `inner_sum_eq`), which is
`≫ X / log² X`, contradicting the claimed `≪ X / (f log³ X)` (`uremCE_final_ineq`).

Defect 2 persists even if defect 1 is repaired (quantifying `A'`, `B` existentially), because the
indicator of the primes satisfies the genuine Siegel–Walfisz theorem; that last remark is
informal (Siegel–Walfisz is not formalized here).  In the actual physical source the primes of
`A·B` divide `f = a_j W q₀` and are therefore excluded from the moduli by `(f, lr) = 1`.
-/

open Finset Real

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

/-! ### The scalar coefficient at a small prime -/

theorem Bcoef_eq_zero_of_not_goodHigh (S : ScalarParams) {J a : ℕ} (P : Fin J → Fin S.H)
    (h : ¬ S.GoodHigh J a) : S.Bcoef J P a = 0 := by
  simp [Bcoef, Tcount_eq_zero P h]

theorem Bcoef_zero_one (S : ScalarParams) (P : Fin 0 → Fin S.H) : S.Bcoef 0 P 1 = 1 := by
  classical
  unfold Bcoef Tcount gammaP tuples
  simp [Finset.filter_singleton, Function.injective_of_subsingleton]

/-- **`ℓ_X(3) = -1`** once `3` is a low prime and `27 ≤ D_low`: only the `J = 0` term with
`κ_0(3) = λ⁺_low(3) = μ(3)` survives. -/
theorem ellX_three {S : ScalarParams} (hS : S.Good) (h3 : (3 : ℝ) < S.u0)
    (h27 : (27 : ℝ) ≤ S.Dlow) : S.ellX 3 = -1 := by
  classical
  have hk : S.kappa 0 3 = -1 := by
    have : S.kappa 0 = S.lamLowPlus := by simp [kappa]
    rw [this, lamLowPlus, if_pos]
    · simp [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    refine ⟨Nat.prime_three.squarefree, ?_, ?_⟩
    · simp [Nat.prime_three.primeFactors]; exact_mod_cast h3
    · intro p hp _
      simp [Nat.prime_three.primeFactors] at hp
      subst hp
      simp [above, Nat.prime_three.primeFactors, Finset.filter_singleton]
      norm_num; linarith
  have hB3 : ∀ J (P : Fin J → Fin S.H), S.Bcoef J P 3 = 0 := by
    intro J P
    apply Bcoef_eq_zero_of_not_goodHigh
    rintro ⟨-, hh, -⟩
    exact not_low_of_high hS (hh 3 (by simp [Nat.prime_three.primeFactors]))
      (by exact_mod_cast h3)
  have hB1 : ∀ J (P : Fin J → Fin S.H), J ≠ 0 → S.Bcoef J P 1 = 0 := by
    intro J P hJ
    apply Bcoef_eq_zero_of_not_goodHigh
    rintro ⟨-, -, hc⟩
    simp at hc; exact hJ hc.symm
  have hanti : (3 : ℕ).divisorsAntidiagonal = {(1, 3), (3, 1)} := by decide
  unfold ellX
  rw [Finset.sum_eq_single 0]
  · rw [Fintype.sum_unique, if_pos ⟨fun a _ _ => a.elim0, fun i => i.elim0⟩, hanti,
      sum_pair (by decide)]
    simp [hB3, Bcoef_zero_one, hk]
  · intro J _ hJ
    refine Finset.sum_eq_zero (fun P _ => ?_)
    split_ifs
    · rw [hanti, sum_pair (by decide)]; simp [hB3, hB1 J P hJ]
    · rfl
  · intro h; simp at h

theorem colProd_three_eq_zero {S : ScalarParams} (hS : S.Good) (h3 : (3 : ℝ) < S.u0) {J : ℕ}
    (P : Fin J → Fin S.H) (c : ℕ → Fin 3) (χ : Fin S.Kc → Fin 3) :
    (S.colFactor J P c χ 1 * S.colFactor J P c χ 2) 3 = 0 := by
  have hz : ∀ k : Fin 3, S.colFactor J P c χ k 3 = 0 := by
    intro k
    by_contra h
    obtain ⟨-, hp, -⟩ := colFactor_support hS h
    exact not_low_of_high hS (hp 3 Nat.prime_three dvd_rfl).1 (by exact_mod_cast h3)
  rw [ArithmeticFunction.mul_apply]
  have : (3 : ℕ).divisorsAntidiagonal = {(1, 3), (3, 1)} := by decide
  rw [this, sum_pair (by decide)]
  simp [hz]

theorem sum_coefAtom_three_one {S : ScalarParams} (hS : S.Good) (h3 : (3 : ℝ) < S.u0)
    (h27 : (27 : ℝ) ≤ S.Dlow) (δ N Γ : ℝ) :
    ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
      physCoefAtom S δ N Γ 2 J P χ 3 1 = -Γ := by
  classical
  have h := physCoefAtom_reassemble hS δ N Γ 2 4 (fun d => if d = 3 then 1 else 0)
  have hI : Ico 1 4 = {1, 2, 3} := by decide
  have h13 : ∀ J (P : Fin J → Fin S.H) χ, physCoefAtom S δ N Γ 2 J P χ 1 3 = 0 := by
    intro J P χ
    unfold physCoefAtom
    split_ifs
    · rw [colProd_three_eq_zero hS h3]; simp
    · rfl
  rw [hI] at h
  simp [h13, ellX_three hS h3 h27] at h
  rw [h, if_pos ⟨1, rfl⟩]

theorem physUrem_eq_three {S : ScalarParams} (hS : S.Good) (h3 : (3 : ℝ) < S.u0)
    (h27 : (27 : ℝ) ≤ S.Dlow) (δ N Γ : ℝ) (K' : ℕ) (α β : ArithmeticFunction ℝ) :
    physUrem S δ N Γ 2 1 1 3 4 K' α β =
      -Γ * ∑ v ∈ range K', (α * β) v * (resMask 2 1 v * (hz 1 3 3 v * Uz 1 v)) := by
  classical
  have hz1 : ∀ v, hz 1 3 1 v = 0 := by
    intro v; simp [hz, Iz, Uz, Int.modEq_one]
  have hc2 : ∀ J (P : Fin J → Fin S.H) χ r, physCoefAtom S δ N Γ 2 J P χ 2 r = 0 := by
    intro J P χ r
    unfold physCoefAtom
    rw [if_neg]
    rintro ⟨-, h⟩
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 r) h
    norm_num at this
  have hI : Ico 1 4 = {1, 2, 3} := by decide
  unfold physUrem
  rw [hI]
  simp [physCoefCut, hz1, hc2]
  rw [← neg_mul, ← sum_coefAtom_three_one hS h3 h27 δ N Γ]
  simp only [Finset.sum_mul]

/-! ### Elementary counting: a Chebyshev-type lower bound and a dyadic pigeonhole -/

theorem centralBinom_le_pow_primes (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ ((range (2 * n + 1)).filter Nat.Prime).card := by
  rw [← Nat.prod_pow_factorization_centralBinom n]
  rw [← Finset.prod_filter_mul_prod_filter_not (range (2 * n + 1)) Nat.Prime]
  have h1 : ∏ x ∈ (range (2 * n + 1)).filter (fun p => ¬ p.Prime),
      x ^ n.centralBinom.factorization x = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [Nat.factorization_eq_zero_of_not_prime _ (mem_filter.1 hp).2, pow_zero]
  rw [h1, mul_one, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro p _
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact Nat.pow_factorization_choose_le (by omega)

/-- Chebyshev-type bound `2^m ≤ m (π(2^m) + 1)`. -/
theorem two_pow_le_primes (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m ≤ m * (((range (2 ^ m + 1)).filter Nat.Prime).card + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hn : 0 < 2 ^ k := by positivity
  have e : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  have h1 := Nat.four_pow_le_two_mul_self_mul_centralBinom (2 ^ k) hn
  have h2 := centralBinom_le_pow_primes (2 ^ k) hn
  rw [e] at h1 h2
  set c := ((range (2 ^ (k + 1) + 1)).filter Nat.Prime).card
  have h3 : 2 ^ (2 ^ (k + 1)) ≤ 2 ^ ((k + 1) * (c + 1)) := by
    calc 2 ^ (2 ^ (k + 1)) = 4 ^ (2 ^ k) := by
            rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
      _ ≤ 2 ^ (k + 1) * (2 ^ k).centralBinom := h1
      _ ≤ 2 ^ (k + 1) * (2 ^ (k + 1)) ^ c := Nat.mul_le_mul_left _ h2
      _ = 2 ^ ((k + 1) * (c + 1)) := by rw [← pow_mul, ← pow_add]; ring_nf
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

/-- Number of primes in `[a, b)`, as a real number. -/
noncomputable def primeCnt (a b : ℕ) : ℝ := ∑ n ∈ Ico a b, if n.Prime then (1 : ℝ) else 0

theorem primeCnt_blocks (r k : ℕ) :
    ∑ i ∈ range k, primeCnt (2 ^ (r + i)) (2 ^ (r + i + 1)) = primeCnt (2 ^ r) (2 ^ (r + k)) := by
  induction k with
  | zero => simp [primeCnt]
  | succ k ih =>
    rw [sum_range_succ, ih, primeCnt, primeCnt, primeCnt, ← add_assoc,
      Finset.sum_Ico_consecutive]
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem primeCnt_nonneg (a b : ℕ) : 0 ≤ primeCnt a b :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem primeCnt_le (a b : ℕ) : primeCnt a b ≤ (b : ℝ) - a ∨ b < a := by
  rcases le_or_gt a b with h | h
  · left
    calc primeCnt a b ≤ ∑ n ∈ Ico a b, (1 : ℝ) :=
          Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
      _ = (b : ℝ) - a := by simp [Nat.cast_sub h]
  · right; exact h

theorem primeCnt_big (r : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ (2 * r) / (2 * r) - 2 - 2 ^ r ≤ primeCnt (2 ^ r) (2 ^ (2 * r)) := by
  have h := two_pow_le_primes (2 * r) (by omega)
  set c := ((range (2 ^ (2 * r) + 1)).filter Nat.Prime).card with hc
  have hle1 : 2 ^ r ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcR : (c : ℝ) = primeCnt 0 (2 ^ r) + primeCnt (2 ^ r) (2 ^ (2 * r)) +
      primeCnt (2 ^ (2 * r)) (2 ^ (2 * r) + 1) := by
    unfold primeCnt
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle1,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_succ _), hc, Finset.card_filter,
      Finset.range_eq_Ico]
    push_cast; rfl
  have h1 : primeCnt 0 (2 ^ r) ≤ 2 ^ r := by
    rcases primeCnt_le 0 (2 ^ r) with h | h
    · simpa using h
    · exact absurd h (Nat.not_lt_zero _)
  have h2 : primeCnt (2 ^ (2 * r)) (2 ^ (2 * r) + 1) ≤ 1 := by
    rcases primeCnt_le (2 ^ (2 * r)) (2 ^ (2 * r) + 1) with h | h
    · push_cast at h; linarith
    · omega
  have hR : (2 : ℝ) ^ (2 * r) ≤ (2 * r) * (c + 1) := by exact_mod_cast h
  have hr' : (0 : ℝ) < 2 * r := by positivity
  have h3 : (2 : ℝ) ^ (2 * r) / (2 * r) ≤ c + 1 := by rw [div_le_iff₀' hr']; exact hR
  linarith

/-- **Dyadic pigeonhole**: some block `[2^i, 2^{i+1})`, `r ≤ i < 2r`, carries at least the
average number of primes. -/
theorem exists_prime_block (r : ℕ) (hr : 1 ≤ r) : ∃ i, r ≤ i ∧ i < 2 * r ∧
    ((2 : ℝ) ^ (2 * r) / (2 * r) - 2 - 2 ^ r) / r ≤ primeCnt (2 ^ i) (2 ^ (i + 1)) := by
  have hsum := primeCnt_blocks r r
  rw [show r + r = 2 * r by ring] at hsum
  have hb := primeCnt_big r hr
  have hne : (range r).Nonempty := ⟨0, by simp; omega⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => ((2 : ℝ) ^ (2 * r) / (2 * r) - 2 - 2 ^ r) / r)
    (g := fun i => primeCnt (2 ^ (r + i)) (2 ^ (r + i + 1))) (by
      rw [hsum, sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hr'.ne']
      exact hb)
  exact ⟨r + j, by omega, by simp at hj; omega, hle⟩

/-- Odd multiples of `3` (i.e. `m ≡ 3 mod 6`) in `[M, 2M)`: at least `M/6 - 3` of them. -/
theorem mod6_count_ge (M : ℕ) (hM : 9 ≤ M) :
    (M : ℝ) / 6 - 3 ≤ ∑ m ∈ Ico M (2 * M), if m % 6 = 3 then (1 : ℝ) else 0 := by
  classical
  rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
  set k := (M - 9) / 6
  have hk : k ≤ ((Ico M (2 * M)).filter (fun m => m % 6 = 3)).card := by
    apply Finset.le_card_of_inj_on_range (fun j => 6 * (M / 6 + 1 + j) + 3)
    · intro j hj
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨by omega, by omega⟩, by omega⟩
    · intro i _ j _ h; omega
  have hk' : ((M : ℝ) - 9) / 6 - 1 ≤ k := by
    have h6 : M - 9 < 6 * (k + 1) := by omega
    have : ((M - 9 : ℕ) : ℝ) < 6 * ((k : ℝ) + 1) := by exact_mod_cast h6
    rw [Nat.cast_sub hM] at this
    push_cast at this
    linarith
  have : (k : ℝ) ≤ ((Ico M (2 * M)).filter (fun m => m % 6 = 3)).card := by exact_mod_cast hk
  linarith

/-- The final real inequality: the main term beats the claimed `X / log³ X` bound. -/
theorem uremCE_final_ineq {r : ℕ} {Y CW lg cnt Q : ℝ} (hr : 1 ≤ r) (hY : 8 * r ≤ Y)
    (hlg : 1 / 2 < lg) (hCW0 : 0 ≤ CW) (hCW : CW < r)
    (hcnt : (Y ^ 2 / (2 * r) - 2 - Y) / r ≤ cnt) (hcnt0 : 0 ≤ cnt) (hQ : Y ^ 4 / 6 - 3 ≤ Q) :
    CW * Y ^ 6 / (2 * (6 * r * lg) ^ 3) < cnt * Q := by
  set R : ℝ := (r : ℝ) with hRdef
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hr
  have hR0 : (0 : ℝ) < R := by linarith
  have hY8 : (8 : ℝ) ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  -- lower bound for `cnt`
  have hc1 : Y ^ 2 / (3 * R ^ 2) ≤ cnt := by
    refine le_trans ?_ hcnt
    rw [div_le_div_iff₀ (by positivity) hR0, div_sub' (by positivity), div_sub' (by positivity),
      div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h : 12 * R + 6 * R * Y ≤ Y ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.2 h)]
  have hQ1 : Y ^ 4 / 7 ≤ Q := by
    refine le_trans ?_ hQ
    have : (8 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY8 4
    nlinarith
  have hlow : Y ^ 6 / (21 * R ^ 2) ≤ cnt * Q := by
    calc Y ^ 6 / (21 * R ^ 2) = (Y ^ 2 / (3 * R ^ 2)) * (Y ^ 4 / 7) := by
          field_simp; ring
      _ ≤ cnt * Q := mul_le_mul hc1 hQ1 (by positivity) hcnt0
  have hden : 27 * R ^ 3 ≤ (6 * R * lg) ^ 3 := by
    have : 3 * R ≤ 6 * R * lg := by nlinarith
    calc 27 * R ^ 3 = (3 * R) ^ 3 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) this 3
  have hup : CW * Y ^ 6 / (2 * (6 * R * lg) ^ 3) ≤ CW * Y ^ 6 / (54 * R ^ 3) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have hup2 : CW * Y ^ 6 / (54 * R ^ 3) < Y ^ 6 / (21 * R ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hY6 : 0 < Y ^ 6 := by positivity
    have h1 : CW * (21 * R ^ 2) < R * (21 * R ^ 2) :=
      mul_lt_mul_of_pos_right hCW (by positivity)
    have h2 : CW * (21 * R ^ 2) < 54 * R ^ 3 := by nlinarith
    calc CW * Y ^ 6 * (21 * R ^ 2) = Y ^ 6 * (CW * (21 * R ^ 2)) := by ring
      _ < Y ^ 6 * (54 * R ^ 3) := mul_lt_mul_of_pos_left h2 hY6
  linarith

/-! ### The explicit bilinear data -/

/-- `α`: the indicator of the primes in `[N, 2N)`. -/
noncomputable def ceAlpha (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Prime ∧ N ≤ n ∧ n < 2 * N then 1 else 0, by simp [Nat.not_prime_zero]⟩

/-- `β`: the indicator of the odd multiples of `3` in `[M, 2M)`. -/
noncomputable def ceBeta (M : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if M ≤ m ∧ m < 2 * M ∧ m % 6 = 3 then 1 else 0, by simp⟩

theorem ceAlpha_apply (N n : ℕ) :
    ceAlpha N n = if n.Prime ∧ N ≤ n ∧ n < 2 * N then 1 else 0 := rfl

theorem ceBeta_apply (M m : ℕ) :
    ceBeta M m = if M ≤ m ∧ m < 2 * M ∧ m % 6 = 3 then 1 else 0 := rfl

/-- On the support of `α ⊗ β`, the weight `1_{v ≡ 1 (2)} h_3(v) U_1(v)` (with `A = 1`,
`B = 3`) is identically `1`: there is **no cancellation** in `h_3 = I_3 - U_3`. -/
theorem weight_eq_one {n m : ℕ} (hn : n.Prime) (hn3 : 3 ≤ n) (hm : m % 6 = 3) :
    resMask 2 1 (m * n) * (hz 1 3 3 (m * n) * Uz 1 (m * n)) = 1 := by
  have hn2 : n % 2 = 1 := by
    by_contra hc
    rcases hn.eq_one_or_self_of_dvd 2 (by omega) with h | h
    · omega
    · omega
  have hres : resMask 2 1 (m * n) = 1 := by
    unfold resMask; rw [if_pos]
    unfold Nat.ModEq
    exact Nat.odd_iff.1 (Nat.odd_mul.2 ⟨Nat.odd_iff.2 (by omega), Nat.odd_iff.2 hn2⟩)
  have h3 : 3 ∣ m * n := dvd_mul_of_dvd_left (by omega) n
  have hI : Iz 1 3 3 (m * n) = 1 := by
    unfold Iz; rw [if_pos]
    apply Int.modEq_iff_dvd.2
    have : (3 : ℤ) ∣ ((m * n : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h3
    simpa using dvd_sub (dvd_refl (3 : ℤ)) this
  have hU3 : Uz 3 (m * n) = 0 := by
    unfold Uz; rw [if_neg]
    intro hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc.symm h3
  have hU1 : Uz 1 (m * n) = 1 := by simp [Uz]
  rw [hres, hz, hI, hU3, hU1]; norm_num

/-- **The inner sum, evaluated**: `∑_{v < 4NM} (α * β)(v) 1_{v≡1(2)} h_3(v) U_1(v)
= π[N, 2N) · #{m ∈ [M, 2M) : m ≡ 3 (6)}`. -/
theorem inner_sum_eq (N M : ℕ) (hN : 3 ≤ N) :
    ∑ v ∈ range (4 * N * M), (ceAlpha N * ceBeta M) v *
        (resMask 2 1 v * (hz 1 3 3 v * Uz 1 v)) =
      primeCnt N (2 * N) * ∑ m ∈ Ico M (2 * M), if m % 6 = 3 then (1 : ℝ) else 0 := by
  rw [sum_conv_dyadic (ceAlpha N) (ceBeta M) (N := N) (M := M)
    (fun n h => by rw [ceAlpha_apply] at h; split_ifs at h with h' <;> [exact h'.2; exact absurd rfl h])
    (fun m h => by rw [ceBeta_apply] at h; split_ifs at h with h' <;> [exact ⟨h'.1, h'.2.1⟩; exact absurd rfl h])
    le_rfl]
  rw [primeCnt, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
  rw [mem_Ico] at hn hm
  rw [ceAlpha_apply, ceBeta_apply]
  by_cases hp : n.Prime
  · by_cases h6 : m % 6 = 3
    · rw [if_pos ⟨hp, hn⟩, if_pos ⟨hm.1, hm.2, h6⟩, if_pos hp, if_pos h6,
        weight_eq_one hp (by omega) h6]; ring
    · rw [if_neg (show ¬ (M ≤ m ∧ m < 2 * M ∧ m % 6 = 3) from fun h => h6 h.2.2), if_neg h6]
      ring
  · rw [if_neg (show ¬ (n.Prime ∧ N ≤ n ∧ n < 2 * N) from fun h => hp h.1), if_neg hp]; ring

/-! ### The scale family `X = 2^{6r}` -/

theorem two_pow_rpow (r : ℕ) (e : ℝ) :
    ((2 : ℝ) ^ (6 * r)) ^ e = (2 : ℝ) ^ ((6 * r : ℝ) * e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf

/-- `X^e → ∞` along `X = 2^{6r}`. -/
theorem eventually_le_two_pow_rpow {e : ℝ} (he : 0 < e) (B : ℝ) :
    ∀ᶠ r : ℕ in Filter.atTop, B ≤ ((2 : ℝ) ^ (6 * r)) ^ e := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ (6 * e) := Real.one_lt_rpow (by norm_num) (by positivity)
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt h1).eventually_ge_atTop B] with r hr
  rw [two_pow_rpow]
  convert hr using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf

/-- `u = X^{(59/100) ε₀² / (1+ε₀+τ)}`. -/
theorem u0_eq_rpow {S : ScalarParams} (hS : S.Good) :
    S.u0 = S.X ^ ((59 / 100 : ℝ) * (1 / (1 + S.eps0 + S.tau)) * S.eps0 ^ 2) := by
  have hX : 0 ≤ S.X := by linarith [hS.X_gt]
  unfold u0 Dint Dtot
  rw [← Real.rpow_mul hX, ← Real.rpow_mul hX]

theorem eight_mul_le_two_pow {r : ℕ} (hr : 6 ≤ r) : 8 * r ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-! ### The counterexample -/

/-- **`OrdinaryBVUremProviderScoped κ` is false** for every `κ ∈ (0, 10⁻⁵)` (i.e. whenever the
critical regime is non-empty).

Witness: affine data `A = 1`, `B = 3`; base `f = 2`, `c = 1`; cutoff `K = 4`; roughness
`ρ = 3κ`; `Aexp = 3`; and the user-chosen Siegel–Walfisz parameters `A' = B = 0`, which make
`SWSeqMasked` vacuous (only `q = 1`).  At `X = 2^{6r}`, `N = 2^i` (a prime-rich dyadic block),
`M = 2^{6r-i-1}`, `α = 1_{primes ∼ N}`, `β = 1_{m ∼ M, m ≡ 3 (6)}`, the `h_l U_r` part equals
`-π[N,2N) · #{m ∼ M : m ≡ 3 (6)} ≫ X / log² X`, because the only surviving modulus is `l = 3`,
which divides `B`, so `h_3 = I_3 - U_3 ≡ 1` on the support (no cancellation). -/
theorem not_ordinaryBVUremProviderScoped {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) :
    ¬ OrdinaryBVUremProviderScoped κ := by
  intro hprov
  obtain ⟨C, X0, hC⟩ := hprov 1 3 one_pos (by norm_num) (by norm_num) (3 * κ) (by positivity)
    3 0 0 0
  set T := Tchoice κ with hT
  set S0 : ScalarParams := ⟨2, T⟩ with hS0
  have hS0g : S0.Good := (critRegime_Tchoice hκ hκ' (by norm_num : (1 : ℝ) < 2)).good
  set W : ℝ := ∑ J ∈ range (T ^ 2 + 1), (S0.H : ℝ) ^ J * 3 ^ J with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by positivity)
  set CW : ℝ := max C 0 * W with hCW
  set c0 : ℝ := (59 / 100 : ℝ) * (1 / (1 + S0.eps0 + S0.tau)) * S0.eps0 ^ 2 with hc0
  have hc0pos : 0 < c0 := by
    have := eps0_pos hS0g; have := tau_pos hS0g
    rw [hc0]; positivity
  -- eventual conditions on `r`
  have hev : ∀ᶠ r : ℕ in Filter.atTop,
      X0 ≤ ((2 : ℝ) ^ (6 * r)) ^ (1 : ℝ) ∧ 7 ≤ ((2 : ℝ) ^ (6 * r)) ^ c0 ∧
      2 ≤ ((2 : ℝ) ^ (6 * r)) ^ sigmaBase κ ∧ 6 ≤ r ∧ CW < r :=
    (eventually_le_two_pow_rpow one_pos X0).and ((eventually_le_two_pow_rpow hc0pos 7).and
      ((eventually_le_two_pow_rpow (by unfold sigmaBase; positivity) 2).and
      ((Filter.eventually_ge_atTop 6).and
      (tendsto_natCast_atTop_atTop.eventually_gt_atTop CW))))
  obtain ⟨r, hX0r, hu0r, hfr, hr6, hCWr⟩ := hev.exists
  rw [Real.rpow_one] at hX0r
  set X : ℝ := (2 : ℝ) ^ (6 * r) with hXdef
  set S : ScalarParams := ⟨X, T⟩ with hSdef
  have hX1 : 1 < X := one_lt_pow₀ (by norm_num) (by omega)
  have hreg : CritRegime S κ := critRegime_Tchoice hκ hκ' hX1
  have hSg := hreg.good
  have hH : S.H = S0.H := H_eq_of_T hSg hS0g rfl
  have hu0 : (6 : ℝ) < S.u0 := by
    rw [u0_eq_rpow hSg]
    exact lt_of_lt_of_le (by norm_num) hu0r
  have h3 : (3 : ℝ) < S.u0 := by linarith
  have h27 : (27 : ℝ) ≤ S.Dlow := le_trans (by nlinarith) (u0_sq_le_Dlow hSg)
  obtain ⟨i, hri, hi2r, hcnt⟩ := exists_prime_block r (by omega)
  set Nn : ℕ := 2 ^ i with hNn
  set M : ℕ := 2 ^ (6 * r - i - 1) with hM
  have hNM : Nn * M = 2 ^ (6 * r - 1) := by
    rw [hNn, hM, ← pow_add]; congr 1; omega
  have hNn3 : 3 ≤ Nn := by
    have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [hNn]; omega
  have hM9 : 2 ^ (4 * r) ≤ M := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h16 : 16 ≤ 2 ^ (4 * r) := by
    have : 2 ^ 4 ≤ 2 ^ (4 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  -- the lower end of the critical cell, also used for roughness
  have hlo : X ^ (3 * κ) ≤ (Nn : ℝ) := by
    rw [hXdef, two_pow_rpow, hNn]
    push_cast
    calc (2 : ℝ) ^ (6 * (r : ℝ) * (3 * κ)) ≤ (2 : ℝ) ^ (r : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = (2 : ℝ) ^ r := Real.rpow_natCast _ _
      _ ≤ (2 : ℝ) ^ i := pow_le_pow_right₀ (by norm_num) hri
  have hcell : CritCell S κ (Nn : ℝ) := by
    refine ⟨hlo, ?_⟩
    show ((2 ^ i : ℕ) : ℝ) ≤ X ^ (1 / 3 + κ / 2)
    rw [hXdef, two_pow_rpow]
    push_cast
    calc (2 : ℝ) ^ i = (2 : ℝ) ^ (i : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (6 * (r : ℝ) * (1 / 3 + κ / 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (i : ℝ) ≤ 2 * r := by exact_mod_cast hi2r.le
          nlinarith
  have hNMX : (Nn : ℝ) * M ≤ S.X := by
    show (Nn : ℝ) * M ≤ X
    have : Nn * M ≤ 2 ^ (6 * r) := by
      rw [hNM]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hXdef]; exact_mod_cast this
  have hXNM : S.X ≤ 4 * ((Nn : ℝ) * M) := by
    show X ≤ 4 * ((Nn : ℝ) * M)
    have : 2 ^ (6 * r) ≤ 4 * (Nn * M) := by
      have e : 2 ^ (6 * r) = 2 * 2 ^ (6 * r - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hNM, e]; omega
    rw [hXdef]; exact_mod_cast this
  have hf : ((2 : ℕ) : ℝ) ≤ S.X ^ sigmaBase κ := by exact_mod_cast hfr
  have hαb : ∀ m, |ceAlpha Nn m| ≤ 1 := by
    intro m; rw [ceAlpha_apply]; split_ifs <;> norm_num
  have hβb : ∀ m, |ceBeta M m| ≤ 1 := by
    intro m; rw [ceBeta_apply]; split_ifs <;> norm_num
  have hαs : ∀ m, ceAlpha Nn m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn := by
    intro m h; rw [ceAlpha_apply] at h
    split_ifs at h with h' <;> [exact h'.2; exact absurd rfl h]
  have hβs : ∀ m, ceBeta M m ≠ 0 → M ≤ m ∧ m < 2 * M := by
    intro m h; rw [ceBeta_apply] at h
    split_ifs at h with h' <;> [exact ⟨h'.1, h'.2.1⟩; exact absurd rfl h]
  have hrough : RoughSupport (ceAlpha Nn) (S.X ^ (3 * κ)) := by
    intro m h p hp hpm
    rw [ceAlpha_apply] at h
    split_ifs at h with h'
    · rw [(Nat.prime_dvd_prime_iff_eq hp h'.1).1 hpm]
      exact hlo.trans (by exact_mod_cast h'.2.1)
    · exact absurd rfl h
  have hsw : SWSeqMasked (ceAlpha Nn) Nn 0 0 (0 * 1) := by
    intro d q a _ hq hqB _
    rw [Real.rpow_zero] at hqB
    have hq1 : q = 1 := by
      have : q ≤ 1 := by exact_mod_cast hqB
      omega
    subst hq1
    simp [Nat.modEq_one]
  have happ := hC S hreg (by simpa using hX0r) Nn M hcell hNMX hXNM 1 2 1 4 (4 * Nn * M)
    two_pos hf (by norm_num) (ceAlpha Nn) (ceBeta M) 1 1 hαb hβb hαs hβs hrough hsw
  rw [physUrem_eq_three hSg h3 h27, inner_sum_eq Nn M hNn3, hH] at happ
  have e2 : 2 * Nn = 2 ^ (i + 1) := by rw [hNn, pow_succ, mul_comm]
  rw [e2] at happ
  have hWS : (∑ J ∈ range (S.T ^ 2 + 1), (S0.H : ℝ) ^ J * 3 ^ J) = W := rfl
  rw [hWS] at happ
  set cnt := primeCnt Nn (2 ^ (i + 1)) with hcntdef
  set Q := ∑ m ∈ Ico M (2 * M), if m % 6 = 3 then (1 : ℝ) else 0 with hQdef
  have hcnt0 : 0 ≤ cnt := primeCnt_nonneg _ _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hQ : ((2 : ℝ) ^ r) ^ 4 / 6 - 3 ≤ Q := by
    have h1 := mod6_count_ge M (by omega)
    have hMY : ((2 : ℝ) ^ r) ^ 4 ≤ (M : ℝ) := by
      rw [← pow_mul, mul_comm r 4]; exact_mod_cast hM9
    linarith
  have hcnt' : (((2 : ℝ) ^ r) ^ 2 / (2 * r) - 2 - 2 ^ r) / r ≤ cnt := by
    rw [← pow_mul, mul_comm r 2]; exact hcnt
  have hlog : Real.log S.X = 6 * r * Real.log 2 := by
    show Real.log X = _
    rw [hXdef, Real.log_pow]; push_cast; ring
  have hX6 : S.X = ((2 : ℝ) ^ r) ^ 6 := by
    show X = _
    rw [hXdef, ← pow_mul, mul_comm r 6]
  have hrp : Real.log S.X ^ (3 : ℝ) = (6 * r * Real.log 2) ^ 3 := by
    rw [hlog, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrp, hX6] at happ
  simp only [mul_one, abs_one, neg_one_mul, abs_neg, Nat.cast_ofNat] at happ
  rw [abs_of_nonneg (mul_nonneg hcnt0 hQ0)] at happ
  have hlg : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hfin := uremCE_final_ineq (r := r) (Y := (2 : ℝ) ^ r) (CW := CW) (lg := Real.log 2)
    (cnt := cnt) (Q := Q) (by omega) (by exact_mod_cast eight_mul_le_two_pow hr6) hlg
    (by rw [hCW]; exact mul_nonneg (le_max_right _ _) hW0) hCWr hcnt' hcnt0 hQ
  have hcmp : C * W * ((2 : ℝ) ^ r) ^ 6 / (2 * (6 * r * Real.log 2) ^ 3) ≤
      CW * ((2 : ℝ) ^ r) ^ 6 / (2 * (6 * r * Real.log 2) ^ 3) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [hCW]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0)
      (by positivity)
  linarith

/-- The older, broader remainder provider is false as well (it implies the scoped one). -/
theorem not_ordinaryBVUremProvider {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) :
    ¬ OrdinaryBVUremProvider κ :=
  fun h => not_ordinaryBVUremProviderScoped hκ hκ' (bvUrem_scoped_of_old h)

/-- The two scoped Type-II providers are jointly inconsistent in the critical regime, so
`scalarTypeII_bound_of_scopedProviders` has an unsatisfiable hypothesis there. -/
theorem scopedProviders_inconsistent {κ : ℝ} (hκ : 0 < κ) (hκ' : κ < 1 / 100000) :
    ¬ (PascadiCriticalCellProviderScoped κ ∧ OrdinaryBVUremProviderScoped κ) :=
  fun h => not_ordinaryBVUremProviderScoped hκ hκ' h.2

/-- **The actual source escapes defect 2**: in a physical packet with `j ≠ ℓ`, every prime
dividing the reduced affine pair `A_{jℓ} · |B_{jℓ}|` divides the base `f_ξ = a_j W q₀`; hence the
condition `(f_ξ, l r) = 1` built into `physCoefAtom` removes every modulus sharing a prime with
`A · B`. -/
theorem PhysData.prime_dvd_f_of_dvd_AB (P : Erdos287.Physical.PhysData) (hP : P.WGood)
    (ξ : Erdos287.Physical.Packet P.k) (hjl : ξ.j ≠ ξ.l) {p : ℕ} (hp : p.Prime)
    (hpAB : p ∣ P.A ξ * (P.B ξ).natAbs) : p ∣ P.f ξ := by
  have hW : p ∣ P.W := by
    rcases (Nat.Prime.dvd_mul hp).1 hpAB with hA | hB
    · refine hP.slope ξ.l p hp (hA.trans ?_)
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
    · have hgd : (P.g ξ : ℤ) ∣ (P.a ξ.l : ℤ) - P.a ξ.j :=
        dvd_sub (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _))
          (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
      have hpB : (p : ℤ) ∣ P.B ξ := Int.natCast_dvd.2 hB
      have : (p : ℤ) ∣ (P.a ξ.l : ℤ) - P.a ξ.j := by
        rw [← Int.ediv_mul_cancel hgd]
        exact Dvd.dvd.mul_right hpB _
      exact hP.diff ξ.l ξ.j (Ne.symm hjl) p hp this
  unfold Erdos287.Physical.PhysData.f
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hW _) _

end Erdos287.Physical.TypeII
