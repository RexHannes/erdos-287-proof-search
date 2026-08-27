import Mathlib
import RequestProject.Erdos287.Uniform
import RequestProject.Erdos287.PlacedLCBeta

/-!
# The log-cofactor asymptotic (`LOG-COFACTOR-ASYMPTOTIC287`)

For a fixed real `η` with `0 < η < 1/2` put

`J(M) = ⌊η · log M / log log M⌋`.

Using only the banked finite bound `C(j) ≤ j · j!` (`Erdos287.C_le_U`), we prove that for
all sufficiently large `M` **every** `q` with `M ≤ 2 J(M) q` satisfies

* `q² > M`, and
* `q > C(2 J(M))`.

Primality of `q` is *not* needed and therefore not assumed (the claim for primes is the
special case).

## Proof ingredients (all proved here, none assumed)

* `log_le_two_sqrt`  : `log x ≤ 2√x`;
* `log_sq_lt_self`   : `(log M)² < M` for `M > 256` (via `log M ≤ 4·M^{1/4}`);
* `Jlog_le`          : `J(M) ≤ η log M / log log M` (floor);
* `two_J_le_log`     : `2J(M) ≤ log M`;
* `log_pow_bound`    : `(2J+2)·log(2J) ≤ 2η log M + 2 log log M < log M`, the
  `log C(2J) ≤ (2η + o(1)) log M` step in explicit form;
* comparison with `M/(2J)` and `M/(2J) > √M` are the two conclusions.

No `sorry`, no axiom, and no external analytic input: the theorem is kernel-checked.
-/

open scoped BigOperators

namespace Erdos287

/-! ## Elementary real estimates -/

/-- `log x ≤ 2√x` for `x > 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [h2] at h1
  linarith

/-- `(log x)² < x` for `x > 256`. -/
theorem log_sq_lt_self {x : ℝ} (hx : (256 : ℝ) < x) : (Real.log x) ^ 2 < x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs : Real.sqrt x > 16 := by
    have : Real.sqrt 256 < Real.sqrt x := Real.sqrt_lt_sqrt (by norm_num) hx
    have h256 : Real.sqrt 256 = 16 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h256 ▸ this]
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  -- `log x = 2 log √x ≤ 4 √(√x)`
  have hlog : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
    have h1 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
    have h2 : Real.log (Real.sqrt x) ≤ 2 * Real.sqrt (Real.sqrt x) := log_le_two_sqrt hs0
    rw [h1] at h2
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
    have := mul_self_le_mul_self hlog0 hlog
    have hss : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
      Real.mul_self_sqrt hs0.le
    nlinarith [this, hss]
  have hfin : 16 * Real.sqrt x < x := by
    have : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  linarith

/-! ## The cutoff `J(M)` -/

/-- `J(M) = ⌊η · log M / log log M⌋`. -/
noncomputable def Jlog (eta : ℝ) (M : ℕ) : ℕ :=
  ⌊eta * Real.log M / Real.log (Real.log M)⌋₊

/-! ## The main asymptotic theorem -/

set_option maxHeartbeats 1000000 in
/-- **`LOG-COFACTOR-ASYMPTOTIC287`.**  For fixed `0 < η < 1/2` there is an effective
threshold `M₀` such that for every `M ≥ M₀` and every `q` with `M ≤ 2 J(M) q` one has
`M < q²` and `C(2 J(M)) < q`.

The threshold is explicit: `M₀ = ⌈exp T⌉ + 257` with
`T = max (17/(1−2η)², 4/η², 6)`. -/
theorem logCofactor_asymptotic287 (eta : ℝ) (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ q : ℕ, M ≤ 2 * Jlog eta M * q →
      M < q ^ 2 ∧ C (2 * Jlog eta M) < (q : ℤ) := by
  have h2eta : 0 < 1 - 2 * eta := by linarith
  set T : ℝ := max (max (17 / (1 - 2 * eta) ^ 2) (4 / eta ^ 2)) 6 with hTdef
  refine ⟨⌈Real.exp T⌉₊ + 257, ?_⟩
  intro M hM q hMq
  -- Basic size facts about `M`.
  have hM257N : (257 : ℕ) ≤ M := by omega
  have hM257 : (257 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM257N
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hexpT : Real.exp T ≤ (M : ℝ) := by
    have h1 : Real.exp T ≤ (⌈Real.exp T⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp T⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by
      have : (⌈Real.exp T⌉₊ : ℕ) ≤ M := by omega
      exact_mod_cast this
    linarith
  set L : ℝ := Real.log M with hLdef
  have hLT : T ≤ L := by
    have := Real.log_le_log (Real.exp_pos T) hexpT
    rwa [Real.log_exp] at this
  have hL6 : (6 : ℝ) ≤ L := le_trans (le_max_right _ _) hLT
  have hL0 : (0 : ℝ) < L := by linarith
  set LL : ℝ := Real.log L with hLLdef
  have hLL1 : (1 : ℝ) ≤ LL := by
    have hexp1 : Real.exp 1 < 6 := by
      have := Real.exp_one_lt_d9
      linarith
    have : Real.log (Real.exp 1) ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) (by linarith)
    rwa [Real.log_exp] at this
  have hLL0 : (0 : ℝ) < LL := by linarith
  have hLLsqrt : LL ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
  have hsqrtL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsqrtLsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  -- Threshold consequences for `√L`.
  have hsqrt_eta : 2 / eta ≤ Real.sqrt L := by
    have hle : (2 / eta) ^ 2 ≤ L := by
      have : 4 / eta ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLT
      calc (2 / eta) ^ 2 = 4 / eta ^ 2 := by rw [div_pow]; norm_num
        _ ≤ L := this
    nlinarith [hsqrtL0, hsqrtLsq, div_pos (by norm_num : (0:ℝ) < 2) heta0]
  have hsqrt_margin : 4 / (1 - 2 * eta) < Real.sqrt L := by
    have hle : (4 / (1 - 2 * eta)) ^ 2 < L := by
      have h17 : 17 / (1 - 2 * eta) ^ 2 ≤ L :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLT
      have heq : (4 / (1 - 2 * eta)) ^ 2 = 16 / (1 - 2 * eta) ^ 2 := by
        rw [div_pow]; norm_num
      have hlt : 16 / (1 - 2 * eta) ^ 2 < 17 / (1 - 2 * eta) ^ 2 := by
        have hc : (0 : ℝ) < (1 - 2 * eta) ^ 2 := by positivity
        gcongr
        norm_num
      rw [heq]
      linarith
    nlinarith [hsqrtL0, hsqrtLsq, div_pos (by norm_num : (0:ℝ) < 4) h2eta]
  -- `M > (log M)²`
  have hMgtL2 : L ^ 2 < (M : ℝ) := log_sq_lt_self (by linarith)
  -- The cutoff `J`.
  set J : ℕ := Jlog eta M with hJdef
  have hJarg : (0 : ℝ) ≤ eta * L / LL := by positivity
  have hJle : (J : ℝ) ≤ eta * L / LL := by
    rw [hJdef, Jlog]
    exact Nat.floor_le hJarg
  have hJ1 : 1 ≤ J := by
    have hLLetaL : LL ≤ eta * L := by
      have : 2 * Real.sqrt L ≤ eta * L := by
        have h2 : 2 ≤ eta * Real.sqrt L := by
          have := (div_le_iff₀ heta0).1 hsqrt_eta
          nlinarith [hsqrtL0]
        nlinarith [hsqrtL0, hsqrtLsq]
      linarith
    have h1le : (1 : ℝ) ≤ eta * L / LL := (one_le_div hLL0).2 hLLetaL
    have : (1 : ℕ) ≤ ⌊eta * L / LL⌋₊ := Nat.le_floor (by exact_mod_cast h1le)
    rwa [hJdef, Jlog]
  have hJ1R : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
  have hJ0 : (0 : ℝ) < (J : ℝ) := by linarith
  have h2J_le_L : 2 * (J : ℝ) ≤ L := by
    have h1 : 2 * (J : ℝ) ≤ 2 * (eta * L / LL) := by linarith
    have h2 : 2 * (eta * L / LL) ≤ L := by
      have heq : 2 * (eta * L / LL) = (2 * eta * L) / LL := by ring
      rw [heq, div_le_iff₀ hLL0]
      nlinarith
    linarith
  -- Part 1: `M < q²`.
  have hqR : (M : ℝ) ≤ 2 * (J : ℝ) * (q : ℝ) := by exact_mod_cast hMq
  have h4J2 : 4 * (J : ℝ) ^ 2 < (M : ℝ) := by nlinarith [hMgtL2, h2J_le_L, hJ0]
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; rw [h, Nat.mul_zero] at hMq; omega
    · exact_mod_cast h
  have hpart1R : (M : ℝ) < (q : ℝ) ^ 2 := by
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := pow_pos hq0 2
    have step1 : (M : ℝ) ^ 2 ≤ 4 * (J : ℝ) ^ 2 * (q : ℝ) ^ 2 := by nlinarith [hqR, hMpos]
    have step2 : 4 * (J : ℝ) ^ 2 * (q : ℝ) ^ 2 < (M : ℝ) * (q : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right h4J2 hq2
    nlinarith [lt_of_le_of_lt step1 step2, hMpos]
  have hpart1 : M < q ^ 2 := by exact_mod_cast hpart1R
  refine ⟨hpart1, ?_⟩
  -- Part 2: `C(2J) < q`.
  have h2J0 : (0 : ℝ) < 2 * (J : ℝ) := by linarith
  have hlog2J : Real.log (2 * (J : ℝ)) ≤ LL := Real.log_le_log h2J0 h2J_le_L
  have hlog2J0 : 0 ≤ Real.log (2 * (J : ℝ)) := by
    have : (1 : ℝ) ≤ 2 * (J : ℝ) := by linarith
    exact Real.log_nonneg this
  -- `(2J+2)·log(2J) < log M`
  have hkey : (2 * (J : ℝ) + 2) * Real.log (2 * (J : ℝ)) < L := by
    have hstep1 : (2 * (J : ℝ) + 2) * Real.log (2 * (J : ℝ)) ≤ (2 * (J : ℝ) + 2) * LL := by
      have : (0 : ℝ) ≤ 2 * (J : ℝ) + 2 := by linarith
      nlinarith
    have hstep2 : (2 * (J : ℝ) + 2) * LL ≤ 2 * eta * L + 2 * LL := by
      have h2Jb : 2 * (J : ℝ) ≤ 2 * eta * L / LL := by
        have : (J : ℝ) ≤ eta * L / LL := hJle
        calc 2 * (J : ℝ) ≤ 2 * (eta * L / LL) := by linarith
          _ = 2 * eta * L / LL := by ring
      have hmul : (2 * (J : ℝ)) * LL ≤ (2 * eta * L / LL) * LL :=
        mul_le_mul_of_nonneg_right h2Jb hLL0.le
      have hcancel : (2 * eta * L / LL) * LL = 2 * eta * L := by field_simp
      nlinarith
    have hstep3 : 2 * eta * L + 2 * LL < L := by
      have h4 : 2 * LL ≤ 4 * Real.sqrt L := by linarith
      have h5 : 4 * Real.sqrt L < (1 - 2 * eta) * L := by
        have := (div_lt_iff₀ h2eta).1 hsqrt_margin
        nlinarith [hsqrtL0, hsqrtLsq]
      linarith
    linarith
  -- exponentiate: `(2J)^(2J+2) < M`
  have hnat2J : ((2 * J : ℕ) : ℝ) = 2 * (J : ℝ) := by push_cast; ring
  have hpowR : ((2 * J : ℕ) : ℝ) ^ (2 * J + 2) < (M : ℝ) := by
    have hlogpow : Real.log (((2 * J : ℕ) : ℝ) ^ (2 * J + 2))
        = ((2 * J + 2 : ℕ) : ℝ) * Real.log ((2 * J : ℕ) : ℝ) := by
      rw [Real.log_pow]
    have hposbase : (0 : ℝ) < ((2 * J : ℕ) : ℝ) := by rw [hnat2J]; linarith
    have hpos : (0 : ℝ) < ((2 * J : ℕ) : ℝ) ^ (2 * J + 2) := by positivity
    have hloglt : Real.log (((2 * J : ℕ) : ℝ) ^ (2 * J + 2)) < Real.log (M : ℝ) := by
      rw [hlogpow, hnat2J]
      have : ((2 * J + 2 : ℕ) : ℝ) = 2 * (J : ℝ) + 2 := by push_cast; ring
      rw [this]
      exact hkey
    exact (Real.log_lt_log_iff hpos hMpos).1 hloglt
  have hpowN : (2 * J) ^ (2 * J + 2) < M := by exact_mod_cast hpowR
  -- factorial bound: `C(2J) ≤ 2J·(2J)! ≤ (2J)^(2J+1)`
  have hfact : Nat.factorial (2 * J) ≤ (2 * J) ^ (2 * J) := Nat.factorial_le_pow _
  have hU : U (2 * J) ≤ (2 * J) ^ (2 * J + 1) := by
    calc U (2 * J) = (2 * J) * Nat.factorial (2 * J) := rfl
      _ ≤ (2 * J) * (2 * J) ^ (2 * J) := Nat.mul_le_mul_left _ hfact
      _ = (2 * J) ^ (2 * J + 1) := by ring
  -- comparison with `q`
  have hlt : (2 * J) ^ (2 * J + 1) < q := by
    have h2Jpos : 0 < 2 * J := by omega
    have hfac : (2 * J) * ((2 * J) ^ (2 * J + 1)) < (2 * J) * q := by
      calc (2 * J) * ((2 * J) ^ (2 * J + 1)) = (2 * J) ^ (2 * J + 2) := by ring
        _ < M := hpowN
        _ ≤ 2 * J * q := hMq
    exact lt_of_mul_lt_mul_left hfac (by omega)
  have hCU : C (2 * J) ≤ (U (2 * J) : ℤ) := C_le_U (2 * J)
  have : (U (2 * J) : ℤ) < (q : ℤ) := by
    have : U (2 * J) < q := lt_of_le_of_lt hU hlt
    exact_mod_cast this
  exact lt_of_le_of_lt hCU this

/-- **Consequence for the repaired supply predicate.**  Above the threshold, the two
"prime-factor" side conditions of `PlacedLCBeta` (`q² > M` and `q > C(2J)`) are automatic:
only the *arithmetic* content — an adjacent pair `x, x+1` in the upper half of `[1,M]`
whose members carry prime factors `≥ M/(2J)` — has to be supplied. -/
theorem placedLCBeta_of_adjacent_large_prime_factors (eta : ℝ) (heta0 : 0 < eta)
    (heta : eta < 1 / 2) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ∀ x q₀ q₁ : ℕ, q₀.Prime → q₁.Prime →
        M ≤ 2 * Jlog eta M * q₀ → M ≤ 2 * Jlog eta M * q₁ →
        q₀ ∣ x → q₁ ∣ (x + 1) → M ≤ 2 * x → x + 1 ≤ M →
        PlacedLCBeta M (Jlog eta M) := by
  obtain ⟨M0, hM0⟩ := logCofactor_asymptotic287 eta heta0 heta
  refine ⟨M0, ?_⟩
  intro M hM x q₀ q₁ hq0 hq1 hl0 hl1 hd0 hd1 hhalf hxM
  obtain ⟨hs0, hC0⟩ := hM0 M hM q₀ hl0
  obtain ⟨hs1, hC1⟩ := hM0 M hM q₁ hl1
  exact ⟨x, q₀, q₁, hq0, hq1, hl0, hl1, hs0, hs1, hC0, hC1, hd0, hd1, hhalf, hxM⟩

end Erdos287
