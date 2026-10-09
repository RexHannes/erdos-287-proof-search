import Mathlib

/-!
# Erdős #287 effectivity — the rank-three operator `Δ_k` (§61)

```
LEGENDRE / MOEBIUS COPRIME COUNT     : KERNEL-PROVED
MOEBIUS × id = TOTIENT               : KERNEL-PROVED
REDUCED-RESIDUE DISCREPANCY IDENTITY : KERNEL-PROVED
PERIODICITY Δ_k(x+1) = Δ_k(x)        : KERNEL-PROVED
```

The rank-three operator is

    Δ_k(x) = ∑_{d ∣ k} μ(d) · P₁({(k/d) x}),      P₁(t) = {t} − 1/2,

with the **strict** sawtooth endpoint convention `P₁(t) = Int.fract t − 1/2` retained from the
banked Bernoulli algebra.  For `k > 1` the `−1/2` terms cancel (`∑_{d ∣ k} μ(d) = 0`), so the
two usual conventions agree, and the exact reduced-residue discrepancy identity holds:

    Δ_k(x) = φ(k)·x − #{ 1 ≤ n ≤ kx : (n,k) = 1 }.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos287
namespace Effectivity

/-! ## §61.1  Arithmetic inputs -/

/-- **`sum_moebius_divisors`.**  `KERNEL-PROVED`.  `∑_{d ∣ m} μ(d) = 1_{m=1}`. -/
theorem sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d) = if m = 1 then 1 else 0 := by
  have h2 : (ArithmeticFunction.moebius * ↑ArithmeticFunction.zeta) m
      = (1 : ArithmeticFunction ℤ) m := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h2
  rw [h2]
  simp [ArithmeticFunction.one_apply]

/-- **`moebius_mul_id_eq_totient`.**  `KERNEL-PROVED`.  `∑_{d ∣ k} μ(d)·(k/d) = φ(k)`. -/
theorem moebius_mul_id_eq_totient {k : ℕ} (hk : 0 < k) :
    ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * ((k / d : ℕ) : ℝ)
      = (Nat.totient k : ℝ) := by
  have hbase : ∀ n : ℕ, n > 0 → ∑ i ∈ n.divisors, ((Nat.totient i : ℕ) : ℝ) = (n : ℝ) := by
    intro n _
    exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) (Nat.sum_totient n)
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun n : ℕ => (Nat.totient n : ℝ)) (g := fun n : ℕ => (n : ℝ))).1 hbase k hk
  rw [← Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℝ) * (y : ℝ))]
  exact h

/-- The multiples of `d` in `[1,N]` are exactly `d·j`, `1 ≤ j ≤ N/d`. -/
lemma multiples_card {d N : ℕ} (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  classical
  have hset : (Finset.Icc 1 N).filter (fun n => d ∣ n)
      = (Finset.Icc 1 (N / d)).image (fun j => d * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at h1
        · exact hj
      · exact (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact h2)
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      · have := (Nat.le_div_iff_mul_le hd).1 hj2
        rw [mul_comm]; exact this
  rw [hset, Finset.card_image_of_injective _ (fun a b hab => by
    exact Nat.eq_of_mul_eq_mul_left hd hab), Nat.card_Icc]
  simp

/-- **`legendre_coprime_count`.**  `KERNEL-PROVED`.  The Legendre/Möbius formula

    #{1 ≤ n ≤ N : (n,k)=1} = ∑_{d ∣ k} μ(d) ⌊N/d⌋. -/
theorem legendre_coprime_count {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ((((Finset.Icc 1 N).filter (fun n => Nat.Coprime n k)).card : ℕ) : ℝ)
      = ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ) := by
  classical
  have hswap : ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * ((N / d : ℕ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors,
          (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← multiples_card (d := d) (N := N) hd0, Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : d ∣ n <;> simp [h]
  have hinner : ∀ n ∈ Finset.Icc 1 N,
      ∑ d ∈ k.divisors, (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)
        = if Nat.Coprime n k then (1 : ℝ) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hset : k.divisors.filter (fun d => d ∣ n) = (Nat.gcd n k).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdk, -⟩, hdn⟩
        exact ⟨Nat.dvd_gcd hdn hdk, Nat.gcd_ne_zero_right hk.ne'⟩
      · rintro ⟨hdg, -⟩
        exact ⟨⟨hdg.trans (Nat.gcd_dvd_right n k), hk.ne'⟩, hdg.trans (Nat.gcd_dvd_left n k)⟩
    rw [← Finset.sum_filter, hset]
    have := sum_moebius_divisors (Nat.gcd n k)
    have hcast : ∑ d ∈ (Nat.gcd n k).divisors, (ArithmeticFunction.moebius d : ℝ)
        = ((if Nat.gcd n k = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := by
      rw [← this]
      push_cast
      rfl
    rw [hcast]
    by_cases h : Nat.Coprime n k
    · rw [if_pos h, if_pos h]
      norm_num
    · rw [if_neg h, if_neg h]
      norm_num
  rw [hswap, Finset.sum_congr rfl hinner, Finset.sum_boole]

/-! ## §61.2  The operator and its discrepancy identity -/

/-- The strict sawtooth `P₁(t) = {t} − 1/2`. -/
noncomputable def P1 (t : ℝ) : ℝ := Int.fract t - 1 / 2

/-- The rank-three operator `Δ_k(x) = ∑_{d ∣ k} μ(d) P₁((k/d) x)`. -/
noncomputable def DeltaOp (k : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * P1 (((k / d : ℕ) : ℝ) * x)

/-- The reduced-residue count `#{1 ≤ n ≤ y : (n,k)=1}`. -/
noncomputable def coprimeCount (k : ℕ) (y : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊y⌋₊).filter (fun n => Nat.Coprime n k)).card

/-- **`DeltaOp_discrepancy_identity`.**  `KERNEL-PROVED`.  The exact reduced-residue
discrepancy identity

    Δ_k(x) = φ(k)·x − #{1 ≤ n ≤ kx : (n,k) = 1}      (k > 1, x ≥ 0). -/
theorem DeltaOp_discrepancy_identity {k : ℕ} (hk : 1 < k) {x : ℝ} (hx : 0 ≤ x) :
    DeltaOp k x = (Nat.totient k : ℝ) * x - (coprimeCount k ((k : ℝ) * x) : ℝ) := by
  have hk0 : 0 < k := by omega
  have hfloor : ∀ d ∈ k.divisors, (⌊(k : ℝ) * x⌋₊ / d : ℕ) = ⌊((k / d : ℕ) : ℝ) * x⌋₊ := by
    intro d hd
    have hdvd : d ∣ k := (Nat.mem_divisors.1 hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hreal : ((k / d : ℕ) : ℝ) * x = ((k : ℝ) * x) / (d : ℝ) := by
      have : ((k / d : ℕ) : ℝ) = (k : ℝ) / (d : ℝ) := by
        rw [Nat.cast_div hdvd (by exact_mod_cast hd0.ne')]
      rw [this]
      ring
    rw [hreal, Nat.floor_div_natCast]
  have hcount : (coprimeCount k ((k : ℝ) * x) : ℝ)
      = ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * (⌊((k / d : ℕ) : ℝ) * x⌋₊ : ℝ) := by
    rw [coprimeCount, legendre_coprime_count hk0 ⌊(k : ℝ) * x⌋₊]
    exact Finset.sum_congr rfl fun d hd => by rw [hfloor d hd]
  have hfl : ∀ d ∈ k.divisors,
      (⌊((k / d : ℕ) : ℝ) * x⌋₊ : ℝ)
        = ((k / d : ℕ) : ℝ) * x - Int.fract (((k / d : ℕ) : ℝ) * x) := by
    intro d _
    have hnn : 0 ≤ ((k / d : ℕ) : ℝ) * x := by positivity
    rw [Int.self_sub_fract]
    exact natCast_floor_eq_intCast_floor hnn
  have hcount' : (coprimeCount k ((k : ℝ) * x) : ℝ)
      = (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * (((k / d : ℕ) : ℝ) * x))
        - ∑ d ∈ k.divisors,
            (ArithmeticFunction.moebius d : ℝ) * Int.fract (((k / d : ℕ) : ℝ) * x) := by
    rw [hcount, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hfl d hd, mul_sub]
  have hmain : (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * (((k / d : ℕ) : ℝ) * x))
      = (Nat.totient k : ℝ) * x := by
    rw [← moebius_mul_id_eq_totient hk0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ => by ring
  have hhalf : ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * (1 / 2 : ℝ) = 0 := by
    rw [← Finset.sum_mul]
    have hzero : ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) = 0 := by
      have h := sum_moebius_divisors k
      rw [if_neg (by omega : ¬ k = 1)] at h
      have hcast : ((∑ d ∈ k.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
        rw [h]
      push_cast at hcast
      exact hcast
    rw [hzero, zero_mul]
  have hDelta : DeltaOp k x
      = ∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius d : ℝ) * Int.fract (((k / d : ℕ) : ℝ) * x) := by
    rw [DeltaOp]
    have hsplit : ∀ d ∈ k.divisors,
        (ArithmeticFunction.moebius d : ℝ) * P1 (((k / d : ℕ) : ℝ) * x)
          = (ArithmeticFunction.moebius d : ℝ) * Int.fract (((k / d : ℕ) : ℝ) * x)
            - (ArithmeticFunction.moebius d : ℝ) * (1 / 2 : ℝ) := by
      intro d _
      rw [P1, mul_sub]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hhalf, sub_zero]
  rw [hcount', hmain, hDelta]
  ring

/-- **`DeltaOp_periodic`.**  `KERNEL-PROVED`.  `Δ_k` has period `1`. -/
theorem DeltaOp_periodic (k : ℕ) (x : ℝ) : DeltaOp k (x + 1) = DeltaOp k x := by
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ k := (Nat.mem_divisors.1 hd).1
  have hshift : ((k / d : ℕ) : ℝ) * (x + 1) = ((k / d : ℕ) : ℝ) * x + ((k / d : ℕ) : ℕ) := by
    ring
  rw [P1, P1, hshift, Int.fract_add_natCast]

end Effectivity
end Erdos287
