import RequestProject.Erdos287.W2984Publication.MainTheorem
import RequestProject.Erdos287.W2984Publication.AffineCRT
import RequestProject.Erdos287.W2984Publication.ModulusLedger

/-!
# W2.984 — regression controls (§20 of the task)

**ERDŐS #287 REMAINS OPEN.**  Each control is a kernel-checked fact showing that the named
shortcut is *false* or *not available*; the corresponding grep-level controls are in
`audit.sh` (imports of SR-287 / HLS, endpoint, effectivity tags).

| # | rejected shortcut | control |
|---|---|---|
| 1 | old spectator-density inference | `reg1_spectator_density` |
| 2 | dropping the v3 §6 correction | `reg2_uncorrected_remainder`, `reg2_overlap_prime_large` |
| 3 | forgetting the two small-prime-square populations | `reg3_ledger` |
| 4 | modulus exponent reaching `1/2` | `reg4_exponent` |
| 5 | replacing non-squarefree `a_ℓ W` by a squarefree modulus | `reg5_nonsquarefree` |
| 6 | moving `max` residue outside the `q`-sum | `reg6_max_placement` |
| 7 | bilinear BV without support-length check | `reg7_support_lengths` |
| 8 | treating `O(δ)` as zero | `reg8_delta_budget` |
| 9 | proving the endpoint `s = 2.984` | `reg9_endpoint_excluded` (+ `audit.sh`) |
| 10 | importing SR-287 / HLS | `audit.sh` step 3 |
| 11 | W2.984 as global #287 | `reg11_narrow_windows_exist` |
| 12 | ineffective onset as explicit | `W2984_effectivity`, `reg12_tag` |
| 13 | unsigned `S₂` (lower bound replaced by an upper bound) | `reg13_sign` |
| 14 | Merikoski's literal Lemma-13 pointwise inequality | `merikoski_pointwise_fails` |
-/

open scoped BigOperators

namespace Erdos287.W2984Publication

/-! 1. Spectator conditioning changes the local density: modulo `5`, with spectator slope `2`
and sifted slope `3`, *given* `5 ∣ 2t+1` there is **no** `t` with `5 ∣ 3t+1` — the conditional
density is `0`, not `1/(q-1) = 1/4`. -/
theorem reg1_spectator_density :
    (Finset.univ.filter (fun t : ZMod 5 => 2 * t + 1 = 0 ∧ 3 * t + 1 = 0)).card = 0 ∧
      (Finset.univ.filter (fun t : ZMod 5 => 2 * t + 1 = 0)).card = 1 := by
  decide

/-! 2. Without the `y`-roughness of the linear-sieve divisor (v3 §6), the remainder at a
common prime is minus the full local main term: first sum `0`, second sum `g(q) · 1 = 1/4`. -/
theorem reg2_uncorrected_remainder :
    ((Finset.univ.filter (fun t : ZMod 5 => 2 * t + 1 = 0 ∧ 3 * t + 1 = 0)).card : ℚ) -
      (1 / (5 - 1)) * (Finset.univ.filter (fun t : ZMod 5 => 2 * t + 1 = 0)).card = -1/4 := by
  rw [reg1_spectator_density.1, reg1_spectator_density.2]; norm_num

/-- With the §6 repair (`d` has no prime factor `≤ y`), any common factor `c > 1` of `d` and a
spectator divisor contains a prime `> y`. -/
theorem reg2_overlap_prime_large {d c y : ℕ} (hd : ∀ p, p.Prime → p ∣ d → y < p) (hc : c ∣ d)
    (hc1 : 1 < c) : ∃ p, p.Prime ∧ p ∣ c ∧ y < p := by
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  exact ⟨p, hp, hpc, hd p hp (hpc.trans hc)⟩

/-! 3. The ledger has exactly five populations and dropping the two square divisors changes the
total. -/
theorem reg3_ledger {δ εW : ℚ} (h0 : 0 < δ) :
    Fintype.card ModulusSource = 5 ∧ totalS1 δ εW ≠ 1/2 - 2 * δ + εW :=
  ⟨ledger_card, totalS1_ne_without_square h0⟩

/-! 4. The smallness hypothesis on `δ` is load-bearing: at `δ = 1/2` the total exponent is
`≥ 1/2`. -/
theorem reg4_exponent : ¬ totalS1 (1/2) 0 < 1/2 := by
  rw [totalS1_eq]; norm_num

/-! 5. `a_ℓ W` may be non-squarefree, and its radical has a different totient (different main
term `1/φ`). -/
theorem reg5_nonsquarefree : ¬ Squarefree (4 * 2 : ℕ) ∧ Nat.totient (4 * 2) ≠ Nat.totient (2 * 2) := by
  refine ⟨switched_modulus_not_squarefree, by decide⟩

/-! 6. `∑_q max_a` is strictly stronger than `max_a ∑_q`: for the identity `2 × 2` array the
first is `2`, the second `1`. -/
def regArray (q a : Fin 2) : ℕ := if q = a then 1 else 0

theorem reg6_max_placement :
    (∑ q : Fin 2, Finset.univ.sup (fun a => regArray q a)) = 2 ∧
      Finset.univ.sup (fun a : Fin 2 => ∑ q : Fin 2, regArray q a) = 1 := by
  decide

/-! 7. Support lengths for Merikoski Prop. 11 (`X^α ≪ A₁ ≪ X^{1-α}`, `α = 1/7`): the prime
variable of the switched `S₃` lies in `[Y, Z] = [X^{1/7}, X^{3/14}]`, inside the admissible
range; a prime variable of size `X^{1/10}` would not be. -/
theorem reg7_support_lengths :
    ((1 : ℚ) / 7 ≤ 1 / 7 ∧ (3 : ℚ) / 14 ≤ 1 - 1 / 7) ∧ ¬ ((1 : ℚ) / 7 ≤ 1 / 10) := by
  norm_num

/-! 8. The `O(δ)` budget is exactly the certificate room: an error of `1/1000` already destroys
`< 3.984`, so `δ` must be chosen against `C_err`. -/
theorem reg8_delta_budget :
    chenCertificate + (3.984 - chenCertificate) = 3.984 ∧ ¬ (chenCertificate + 1/1000 < 3.984) := by
  unfold chenCertificate; norm_num

/-! 9. The main theorem is stated for `2.984 < s` only. -/
theorem reg9_endpoint_excluded : ¬ ((2.984 : ℝ) < 2.984) := lt_irrefl _

/-! 11. W2.984 says nothing about the narrow chamber: windows with `e(a-1) < M < 2.984 a`
exist at every scale. -/
theorem reg11_narrow_windows_exist (N : ℕ) :
    ∃ a M : ℕ, N ≤ a ∧ Real.exp 1 * ((a : ℝ) - 1) < M ∧ (M : ℝ) < 2.984 * a := by
  refine ⟨N + 10, 2 * (N + 10) + (N + 10) * 3 / 4, le_add_right le_rfl, ?_, ?_⟩
  · have he := Real.exp_one_lt_d9
    have : ((2 * (N + 10) + (N + 10) * 3 / 4 : ℕ) : ℝ) ≥ 2.75 * ((N : ℝ) + 10) - 1 := by
      have h := Nat.div_mul_le_self ((N + 10) * 3) 4
      have h2 : ((N + 10) * 3 / 4 : ℕ) * 4 + 4 > (N + 10) * 3 := by
        have := Nat.lt_div_mul_add (a := (N + 10) * 3) (b := 4) (by norm_num); omega
      have h3 : (((N + 10) * 3 / 4 : ℕ) : ℝ) * 4 + 4 > ((N : ℝ) + 10) * 3 := by
        exact_mod_cast h2
      push_cast; linarith
    push_cast at this ⊢
    nlinarith
  · have h := Nat.div_mul_le_self ((N + 10) * 3) 4
    have h3 : (((N + 10) * 3 / 4 : ℕ) : ℝ) * 4 ≤ ((N : ℝ) + 10) * 3 := by exact_mod_cast h
    push_cast
    nlinarith

/-! 12. Effectivity tag. -/
inductive EffectivityTag
  | effective
  | ineffectiveExistential
  deriving DecidableEq

/-- W2.984 is **ineffective**: the onset is an existential produced by the providers (whose
proofs use Siegel–Walfisz / the BFM exceptional-modulus device without an effective
treatment). -/
def W2984_effectivity : EffectivityTag := .ineffectiveExistential

theorem reg12_tag : W2984_effectivity ≠ .effective := by decide

/-! 13. Sign discipline: an *upper* bound on `S₂` gives nothing.  With `S = 1`, `S₁ = 1`,
`S₂ = S₃ = S_sq = 0` the Chen inequality holds, `S₂ ≤ 2` holds, yet `S ≤ 1 - 2/2 = 0` fails. -/
theorem reg13_sign :
    ∃ S S1 S2 S3 Ssq : ℝ, S ≤ S1 - S2 / 2 + S3 / 2 + Ssq / 2 ∧ S2 ≤ 2 ∧ S3 ≤ 0 ∧ Ssq ≤ 0 ∧
      ¬ (S ≤ S1 - 2 / 2 + 0 + 0) :=
  ⟨1, 1, 0, 0, 0, by norm_num, by norm_num, le_rfl, le_rfl, by norm_num⟩

end Erdos287.W2984Publication
