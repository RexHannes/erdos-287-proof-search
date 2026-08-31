import Mathlib
import RequestProject.Erdos287.FixedCertificateSmoothParity
import RequestProject.Erdos287.Ford723BalancedSevenAdapter3221

/-!
# SP-2, Phase 1 — the direct Balanced7 source adapter

`BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45`

## Provenance

The V22 bank introduced `BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45`, the Ford-(7.23)
coefficient family, as a *candidate* source dictionary for the physical Balanced7 slots.
A direct re-reading of the fixed-certificate material in this repository shows that the
Ford-(7.23) family is **not** the literal Balanced7 source: what the repository actually
carries is the *fixed smooth-parity certificate*

```
Erdos287.SmoothParity.truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)
Erdos287.SmoothParity.FixedCertificateSmoothParityPacket
```

with the cell parameters `k = 0`, `J = ∅`.  Accordingly:

```
BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45 : RETRACTED / NOT THE LITERAL SOURCE
BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45 : the replacement (this file)
```

The FM723 adapter file is **not deleted**: it stays banked as historical candidate
provenance, and the retraction is recorded as machine status data in
`Erdos287.SP2Status`.

## The SP-2 fixed certificate

The SP-2 packet is the fixed certificate with metadata

```
k = 0,   J = ∅,   Ω(n) = 7,   r = 3,   s = ±1,
λ = a fixed smooth prime-box cell.
```

`r = 3` is the *divisor depth*: with `Ω(n) = 7` and the cut at `n^{1/2−ε}`, exactly the
divisors that are products of at most three of the seven primes survive the truncation.
This file proves the two finite threshold facts that pin `r = 3`
(`balancedSeven_threeFactor_below_cutoff`, `balancedSeven_fourFactor_above_cutoff`), the
subset-size bookkeeping, and the resulting alternating coefficient `−20`.

## Safety

Nothing here proves the source identity `H_*(n) = ∑_{d ∣ n, d ≤ n^{1/2−ε}} μ(d)`; it is
exactly the `cell_identity` field of the already-existing smooth-parity packet, which is
uninhabited.  Nothing here proves Balanced7 or Erdős #287.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SP2Source

open Erdos287.SmoothParity

/-! ## §1. The SP-2 certificate metadata -/

/-- **`SP2FixedCertificateData`** — the fixed-certificate parameters of the SP-2 packet.

Pure metadata: `k = 0`, `J = ∅`, `Ω(n) = 7`, divisor depth `r = 3`, sign `s = ±1`, and a
fixed smooth prime-box cell `λ` given as seven finite sets of primes. -/
structure SP2FixedCertificateData where
  /-- The certificate level `k`. -/
  k : ℕ
  /-- The (empty) index set `J`. -/
  J : Finset ℕ
  /-- The prescribed number of prime factors. -/
  bigOmega : ℕ
  /-- The divisor depth surviving the truncation. -/
  r : ℕ
  /-- The sign. -/
  s : ℤ
  /-- The fixed smooth prime-box cell. -/
  lam : Fin 7 → Finset ℕ

/-- **`SP2PacketNormalization`** — the finite conditions defining `BALANCED7-SP2-DIRECT-PACKET45`.

All fields are *finite* conditions; `packet_is_fixed` below exhibits a datum satisfying
them, so this is a genuine (inhabited) piece of metadata, not an analytic interface. -/
structure SP2PacketNormalization (C : SP2FixedCertificateData) : Prop where
  /-- `k = 0`. -/
  k_zero : C.k = 0
  /-- `J = ∅`. -/
  J_empty : C.J = ∅
  /-- `Ω(n) = 7`. -/
  omega_seven : C.bigOmega = 7
  /-- The divisor depth is `3`. -/
  depth_three : C.r = 3
  /-- The sign is a unit. -/
  sign_unit : C.s = 1 ∨ C.s = -1
  /-- The cell is literally supported on primes. -/
  cell_prime : ∀ (i : Fin 7), ∀ p ∈ C.lam i, Nat.Prime p

/-- The SP-2 metadata is consistent: an explicit datum satisfies it. -/
theorem sp2_packet_metadata_inhabited :
    ∃ C : SP2FixedCertificateData, SP2PacketNormalization C := by
  refine ⟨⟨0, ∅, 7, 3, 1, fun _ => {2}⟩, ⟨rfl, rfl, rfl, rfl, Or.inl rfl, ?_⟩⟩
  intro i p hp
  simp only [Finset.mem_singleton] at hp
  subst hp
  exact Nat.prime_two

/-! ## §2. The fixed-certificate divisor sum (SOURCE_OPEN) -/

/-- **`sp2_fixedCertificate_divisorSum`.**  `CONDITIONAL / LEAN_PROVED`.

Given the `k = 0`, `J = ∅` cell identity of the smooth-parity packet — the *source*
obligation, which this project does not discharge — the fixed-certificate weight is the
truncated Möbius sum

```
H_*(n) = ∑_{d ∣ n, d ≤ cut n} μ(d).
```

This is the SP-2 restatement of `Erdos287.SmoothParity.smoothParity_missing_source`; the
hypothesis `hcell` is precisely the `cell_identity` field. -/
theorem sp2_fixedCertificate_divisorSum
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    (hcell : ∀ n ∈ sector, Hs n = truncMobius n (cut n))
    {n : ℕ} (hn : n ∈ sector) :
    Hs n = ∑ d ∈ n.divisors.filter (fun d => d ≤ cut n), ArithmeticFunction.moebius d :=
  smoothParity_missing_source hcell hn

/-! ## §3. The divisor-depth threshold `r = 3` -/

/-- The exponent inequality pinning the depth from below: `3/7 < 1/2`. -/
theorem sp2_threeSeventh_lt_half : (3 : ℚ) / 7 < 1 / 2 := by norm_num

/-- The exponent inequality pinning the depth from above: `1/2 < 4/7`. -/
theorem sp2_half_lt_fourSeventh : (1 : ℚ) / 2 < 4 / 7 := by norm_num

/-- **`balancedSeven_threeFactor_below_cutoff`.**  `LEAN_PROVED`.

A divisor made of at most three of the seven primes (so of size at most `Y³`) lies below
the truncation `n^{3/7}`, hence below `n^{1/2−ε}` for small `ε`. -/
theorem balancedSeven_threeFactor_below_cutoff {Y n d : ℝ}
    (hY : (1 : ℝ) ≤ Y) (hn : Y ^ (7 : ℝ) ≤ n) (hd : d ≤ Y ^ (3 : ℝ)) :
    d ≤ n ^ ((3 : ℝ) / 7) := by
  have hY0 : (0 : ℝ) ≤ Y := le_trans zero_le_one hY
  have hpow : (Y ^ (7 : ℝ)) ^ ((3 : ℝ) / 7) = Y ^ (3 : ℝ) := by
    rw [← Real.rpow_mul hY0]
    norm_num
  have hstep : (Y ^ (7 : ℝ)) ^ ((3 : ℝ) / 7) ≤ n ^ ((3 : ℝ) / 7) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hY0 _) hn (by norm_num)
  rw [hpow] at hstep
  exact le_trans hd hstep

/-- **`balancedSeven_fourFactor_above_cutoff`.**  `LEAN_PROVED`.

A divisor made of four or more of the seven primes (so of size at least `Y⁴`) lies
*strictly above* the truncation `n^{1/2}`, once the prime boxes sit at scale `Y ≥ 256`
and `n ≤ 128·Y⁷` (the dyadic upper bound for a product of seven primes in `[Y, 2Y)`).

Together with the previous lemma this pins the divisor depth of the SP-2 packet at
`r = 3`. -/
theorem balancedSeven_fourFactor_above_cutoff {Y n d : ℝ}
    (hY : (256 : ℝ) ≤ Y) (hn0 : (0 : ℝ) ≤ n) (hn : n ≤ 128 * Y ^ (7 : ℝ))
    (hd : Y ^ (4 : ℝ) ≤ d) :
    n ^ ((1 : ℝ) / 2) < d := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (by norm_num) hY
  have hhalf : (0 : ℝ) < Y ^ ((7 : ℝ) / 2) := Real.rpow_pos_of_pos hY0 _
  -- upper bound for `n ^ (1/2)`
  have h1 : n ^ ((1 : ℝ) / 2) ≤ (128 * Y ^ (7 : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hn0 hn (by norm_num)
  have h2 : (128 * Y ^ (7 : ℝ)) ^ ((1 : ℝ) / 2)
      = (128 : ℝ) ^ ((1 : ℝ) / 2) * Y ^ ((7 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hY0.le _),
      ← Real.rpow_mul hY0.le]
    norm_num
  -- `128 ^ (1/2) < 16`
  have h16 : (256 : ℝ) ^ ((1 : ℝ) / 2) = 16 := by
    rw [show (256 : ℝ) = 16 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (16 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : (128 : ℝ) ^ ((1 : ℝ) / 2) < 16 := by
    calc (128 : ℝ) ^ ((1 : ℝ) / 2) < (256 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 16 := h16
  -- lower bound for `d`
  have h4 : (16 : ℝ) ≤ Y ^ ((1 : ℝ) / 2) := by
    rw [← h16]
    exact Real.rpow_le_rpow (by norm_num) hY (by norm_num)
  have h5 : Y ^ (4 : ℝ) = Y ^ ((1 : ℝ) / 2) * Y ^ ((7 : ℝ) / 2) := by
    rw [← Real.rpow_add hY0]
    norm_num
  calc n ^ ((1 : ℝ) / 2) ≤ (128 : ℝ) ^ ((1 : ℝ) / 2) * Y ^ ((7 : ℝ) / 2) := by
        rw [← h2]; exact h1
    _ < 16 * Y ^ ((7 : ℝ) / 2) := by
        exact mul_lt_mul_of_pos_right h3 hhalf
    _ ≤ Y ^ ((1 : ℝ) / 2) * Y ^ ((7 : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_right h4 hhalf.le
    _ = Y ^ (4 : ℝ) := h5.symm
    _ ≤ d := hd

/-! ## §4. Subset bookkeeping and the alternating coefficient -/

/-- **`sp2_balancedSeven_subsetSizes`.**  `LEAN_PROVED` (kernel-decidable).

The subsets of the seven prime labels of size at most `3` — the divisors surviving the
truncation — number `C(7,0)+C(7,1)+C(7,2)+C(7,3) = 1+7+21+35 = 64`, exactly half of the
`128` divisors of a squarefree seven-prime integer. -/
theorem sp2_balancedSeven_subsetSizes :
    ((Finset.univ : Finset (Finset (Fin 7))).filter (fun S => S.card ≤ 3)).card = 64 := by
  decide +kernel

/-- **`sp2_balancedSeven_coefficient_eq_neg20`.**  `LEAN_PROVED` (kernel-decidable).

The alternating divisor-depth coefficient of the SP-2 packet:

```
∑_{j=0}^{3} (−1)^j C(7,j) = 1 − 7 + 21 − 35 = −20.
```
-/
theorem sp2_balancedSeven_coefficient_eq_neg20 :
    ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 7 j : ℤ) = -20 := by
  decide +kernel

/-- The two halves of the divisor lattice are complementary: `64 + 64 = 128`. -/
theorem sp2_divisorLattice_split :
    ((Finset.univ : Finset (Finset (Fin 7))).filter (fun S => S.card ≤ 3)).card +
        ((Finset.univ : Finset (Finset (Fin 7))).filter (fun S => ¬ S.card ≤ 3)).card
      = 128 := by
  decide +kernel

end SP2Source
end Erdos287
