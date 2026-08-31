import Mathlib
import RequestProject.CurrentProgramme.SharedGcdGramSquare

/-!
# §6 — The signed projector: `S1` and `S2`

`CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE`, Section 6.

The projector is the repository's own `Erdos287.SharedGcdGram.lambdaH`,

```
λ_H = μ * Ω_H,   λ_H(d) = ∑_{e ∣ d} μ(d/e) Ω_H(e),
```

for which `sum_lambdaH_divisors` (Möbius inversion) is already banked.

**Source firewall.**  The normalisation

```
supp Ω_H ⊆ {e ~ H},  |Ω_H(e)| ≪ 1,  ∑_e |Ω_H(e)|/e ≪ 1,  ∑_e |Ω_H(e)|/e² ≪ 1/H
```

is *not* available as a theorem anywhere in this repository: `lambdaH` is defined for an
arbitrary `Ω : ℕ → ℝ`.  Consequently every statement below carries the normalisation as an
explicit hypothesis (`hsupp`, `hmass`), and only the *lower* support constraint `Ω_H(e) = 0`
for `e < H` is used — the upper constraint `e < 2H` is never needed.  Nothing here asserts that
such an `Ω_H` is supplied by the source.

Proved here:

* `sum_inv_sq_Icc_le_two` — `∑_{k ≤ X} 1/k² ≤ 2`;
* `sum_abs_moebius_div_le` — `∑_{k ≤ X} |μ(k)|/k ≤ 1 + log X`;
* `lambdaH_S1_pair_le` — the exact factorisation `S1 ≤ (∑_e |Ω(e)|/e)(∑_{k ≤ X/H} |μ(k)|/k)`,
  in which the inner sum is genuinely truncated at `X/H` (no `d ~ H` assumption is used);
* `projector_S1_bound`, `projector_S1_bound_real` — `S1 ≤ c₁(1 + log(X/H))`;
* `projector_S2_bound` — `S2 ≤ 2c₁/H`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset ArithmeticFunction

namespace Erdos287
namespace OneLevelProjector

open Erdos287.SharedGcdGram

/-! ## §6.1  The two elementary reciprocal sums -/

/-- `∑_{1 ≤ k ≤ X} 1/k² ≤ 2 - 1/X` for `X ≥ 1`.  `LEAN_PROVED`. -/
theorem sum_inv_sq_Icc_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (X : ℝ) := by
  induction X, hX using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      have hEq : (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [hEq]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hstep ⊢
    linarith [ih]

/-- `∑_{1 ≤ k ≤ X} 1/k² ≤ 2`.  `LEAN_PROVED`. -/
theorem sum_inv_sq_Icc_le_two (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  · have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have := sum_inv_sq_Icc_le X hX
    have : (0 : ℝ) < 1 / (X : ℝ) := by positivity
    linarith [sum_inv_sq_Icc_le X hX]

/-- `∑_{1 ≤ k ≤ X} |μ(k)|/k ≤ 1 + log X`.  `LEAN_PROVED`. -/
theorem sum_abs_moebius_div_le (X : ℕ) :
    ∑ k ∈ Finset.Icc 1 X, |((moebius k : ℤ) : ℝ)| / (k : ℝ) ≤ 1 + Real.log (X : ℝ) := by
  have hharm : ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    have h := harmonic_le_one_add_log X
    have hcast : ((harmonic X : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 X, (1 : ℝ) / (k : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      exact Finset.sum_congr rfl (fun k _ => by rw [one_div])
    rw [hcast] at h
    exact h
  refine le_trans (Finset.sum_le_sum ?_) hharm
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
  have habs : |((moebius k : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  gcongr

/-! ## §6.2  `S1` — no `d ~ H` assumption -/

/-- **`DET1-ONELEVEL-PROJECTOR-S1S2-45`, exact factorisation of `S1`.**  `LEAN_PROVED`.

For `Ω` supported in `[H, ∞)`,

```
∑_{d ≤ X} |λ_H(d)|/d ≤ (∑_{e ≤ X} |Ω(e)|/e) · (∑_{k ≤ X/H} |μ(k)|/k),
```

the inner Möbius sum being truncated at `⌊X/H⌋`.  The sum over `d` is over *all* `d ≤ X`; no
assumption `d ~ H` is made. -/
theorem lambdaH_S1_pair_le (Om : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hsupp : ∀ e, e < H → Om e = 0) (X : ℕ) :
    ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
      ≤ (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) *
        (∑ k ∈ Finset.Icc 1 (X / H), |((moebius k : ℤ) : ℝ)| / (k : ℝ)) := by
  classical
  -- pointwise divisor bound
  have hpt : ∀ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
      ≤ ∑ x ∈ d.divisorsAntidiagonal,
          (|((moebius x.1 : ℤ) : ℝ)| / (x.1 : ℝ)) * (|Om x.2| / (x.2 : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd.1
    have h1 := abs_lambdaH_le Om d
    have h2 : |lambdaH Om d| / (d : ℝ)
        ≤ (∑ x ∈ d.divisorsAntidiagonal, |((moebius x.1 : ℤ) : ℝ)| * |Om x.2|) / (d : ℝ) := by
      gcongr
    refine le_trans h2 (le_of_eq ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx1 : (0 : ℝ) < (x.1 : ℝ) := by
      have hne : x.1 ≠ 0 := by rintro h; rw [h] at hx; simp at hx; omega
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hx2 : (0 : ℝ) < (x.2 : ℝ) := by
      have hne : x.2 ≠ 0 := by rintro h; rw [h] at hx; simp at hx; omega
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hdd : (d : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hx.1.symm
    rw [hdd]
    field_simp
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hdisj : (↑(Finset.Icc 1 X) : Set ℕ).PairwiseDisjoint
      (fun d => d.divisorsAntidiagonal) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    rw [Nat.mem_divisorsAntidiagonal] at hp hp'
    exact hab (hp.1.symm.trans hp'.1)
  rw [← Finset.sum_biUnion hdisj, biUnion_divisorsAntidiagonal X]
  set F : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p => p.1 * p.2 ≤ X) with hF
  set f : ℕ × ℕ → ℝ :=
    fun p => (|((moebius p.1 : ℤ) : ℝ)| / (p.1 : ℝ)) * (|Om p.2| / (p.2 : ℝ)) with hf
  -- the pairs with a large Möbius variable carry a vanishing `Ω`
  have hzero : ∀ p ∈ F, p ∉ F.filter (fun p => p.1 ≤ X / H) → f p = 0 := by
    intro p hp hpn
    have hp1 : ¬ p.1 ≤ X / H := by
      simp only [Finset.mem_filter, hp, true_and] at hpn
      exact hpn
    have hple : p.1 * p.2 ≤ X := by
      rw [hF, Finset.mem_filter] at hp
      exact hp.2
    have hp2 : p.2 < H := by
      by_contra hcon
      push_neg at hcon
      have hbig : (X / H + 1) * H ≤ p.1 * p.2 :=
        Nat.mul_le_mul (by omega) hcon
      have hXlt : X < (X / H + 1) * H := by
        have h1 := Nat.div_add_mod X H
        have h2 := Nat.mod_lt X hH
        nlinarith [h1, h2]
      omega
    simp [hf, hsupp p.2 hp2]
  rw [← Finset.sum_subset (Finset.filter_subset (fun p => p.1 ≤ X / H) F) hzero]
  have hsub : F.filter (fun p => p.1 ≤ X / H)
      ⊆ (Finset.Icc 1 (X / H)) ×ˢ (Finset.Icc 1 X) := by
    intro p hp
    simp only [Finset.mem_filter, hF, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1.1.1, hp.2⟩, hp.1.1.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)) ?_
  rw [Finset.sum_product]
  refine le_of_eq ?_
  rw [mul_comm, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by simp only [hf, Finset.mul_sum])

/-- **`DET1-ONELEVEL-PROJECTOR-S1S2-45`, `S1`.**  `LEAN_PROVED` (conditional on the mass pin).

```
S1 = ∑_{d ≤ X} |λ_H(d)|/d ≤ c₁ (1 + log ⌊X/H⌋).
``` -/
theorem projector_S1_bound (Om : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hsupp : ∀ e, e < H → Om e = 0) (X : ℕ) (c1 : ℝ)
    (hmass : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ≤ c1) :
    ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
      ≤ c1 * (1 + Real.log ((X / H : ℕ) : ℝ)) := by
  have hmain := lambdaH_S1_pair_le Om hH hsupp X
  have hmoeb := sum_abs_moebius_div_le (X / H)
  have hOmnn : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) :=
    Finset.sum_nonneg (fun e _ => by positivity)
  have hmoebnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 (X / H), |((moebius k : ℤ) : ℝ)| / (k : ℝ) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  calc ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
      ≤ (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)) *
        (∑ k ∈ Finset.Icc 1 (X / H), |((moebius k : ℤ) : ℝ)| / (k : ℝ)) := hmain
    _ ≤ c1 * (∑ k ∈ Finset.Icc 1 (X / H), |((moebius k : ℤ) : ℝ)| / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (le_trans hmass (le_refl _)) hmoebnn
    _ ≤ c1 * (1 + Real.log ((X / H : ℕ) : ℝ)) := by
        have hc1 : (0 : ℝ) ≤ c1 := le_trans hOmnn hmass
        exact mul_le_mul_of_nonneg_left hmoeb hc1

/-- **`S1` with the real logarithm `log(X/H)`.**  `LEAN_PROVED` (conditional on the mass pin).

For `H ≤ X` the truncated logarithm may be replaced by `log(X/H)`; taking `X = CG` this is the
audited bound `S1 ≪ 1 + log(2G/H)`. -/
theorem projector_S1_bound_real (Om : ℕ → ℝ) {H X : ℕ} (hH : 0 < H) (hHX : H ≤ X)
    (hsupp : ∀ e, e < H → Om e = 0) (c1 : ℝ)
    (hmass : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ≤ c1) :
    ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ)
      ≤ c1 * (1 + Real.log ((X : ℝ) / (H : ℝ))) := by
  have hc1 : (0 : ℝ) ≤ c1 :=
    le_trans (Finset.sum_nonneg (fun e _ => by positivity)) hmass
  have hbase := projector_S1_bound Om hH hsupp X c1 hmass
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hdivpos : (0 : ℝ) < ((X / H : ℕ) : ℝ) := by
    have : 1 ≤ X / H := Nat.one_le_div_iff hH |>.mpr hHX
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hle : ((X / H : ℕ) : ℝ) ≤ (X : ℝ) / (H : ℝ) := by
    rw [le_div_iff₀ hHpos]
    have : (X / H) * H ≤ X := Nat.div_mul_le_self X H
    exact_mod_cast this
  have hlog : Real.log ((X / H : ℕ) : ℝ) ≤ Real.log ((X : ℝ) / (H : ℝ)) :=
    Real.log_le_log hdivpos hle
  nlinarith [hbase, hlog, hc1]

/-! ## §6.3  `S2` -/

/-- **`DET1-ONELEVEL-PROJECTOR-S1S2-45`, `S2`.**  `LEAN_PROVED` (conditional on the mass pin).

```
S2 = ∑_{d ≤ X} |λ_H(d)|/d² ≤ 2c₁/H.
```

Again no `d ~ H` assumption: `d` runs over all of `[1,X]`, and the `1/H` saving comes only from
the support of `Ω_H`. -/
theorem projector_S2_bound (Om : ℕ → ℝ) {H : ℕ} (hH : 0 < H)
    (hsupp : ∀ e, e < H → Om e = 0) (X : ℕ) (c1 : ℝ)
    (hmass : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ≤ c1) :
    ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2 ≤ 2 * c1 / (H : ℝ) := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hc1 : (0 : ℝ) ≤ c1 :=
    le_trans (Finset.sum_nonneg (fun e _ => by positivity)) hmass
  have hmain := lambdaH_harmonic_mass_le Om X
  have hsupp' := omega_support_mass_le Om hH hsupp X
  have hOm2 : ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2 ≤ c1 / (H : ℝ) := by
    refine le_trans hsupp' ?_
    calc (1 / (H : ℝ)) * ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ)
        ≤ (1 / (H : ℝ)) * c1 :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = c1 / (H : ℝ) := by ring
  have hmu2 : ∑ k ∈ Finset.Icc 1 X, |((moebius k : ℤ) : ℝ)| / (k : ℝ) ^ 2 ≤ 2 := by
    refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sq_Icc_le_two X)
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
    have habs : |((moebius k : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    gcongr
  have hnn2 : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 X, |((moebius k : ℤ) : ℝ)| / (k : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hOmnn : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun e _ => by positivity)
  calc ∑ d ∈ Finset.Icc 1 X, |lambdaH Om d| / (d : ℝ) ^ 2
      ≤ (∑ e ∈ Finset.Icc 1 X, |Om e| / (e : ℝ) ^ 2) *
        (∑ k ∈ Finset.Icc 1 X, |((moebius k : ℤ) : ℝ)| / (k : ℝ) ^ 2) := hmain
    _ ≤ (c1 / (H : ℝ)) * 2 := by
        refine mul_le_mul hOm2 hmu2 hnn2 (by positivity)
    _ = 2 * c1 / (H : ℝ) := by ring

end OneLevelProjector
end Erdos287
