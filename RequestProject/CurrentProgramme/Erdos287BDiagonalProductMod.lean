import Mathlib
import RequestProject.CurrentProgramme.LevelPairReciprocalNormalForm
import RequestProject.CurrentProgramme.LevelPairProductModulus
import RequestProject.CurrentProgramme.Erdos287Hybrid2ShortEdgeFirewall

/-!
# b-diagonal product-modulus bank — Erdős #287

**The exact algebraic collapse first.**  Everything in §§1–3 below is unconditional integer /
phase algebra; the analytic `Δ`-large-sieve contraction is **not** banked as unconditional —
its inputs are not present in this repository, so it is exposed with explicit hypotheses
exactly as for Hybrid 2 (§4).

Contents.

* §1  `bdiag_crt_inverse_congr`, `bdiag_phase_product_modulus` — the CRT phase combination

  ```
  e_{m₁}( X·(2ebm₂)⁻¹ ) · e_{m₂}( X·(2ebm₁)⁻¹ )  =  e_{m₁m₂}( X·(2eb)⁻¹ ),
  ```

  in the repository's own modular-exponential representation
  (`Erdos287.NormalForm3221.phase`).
* §2  `bdiag_moebius_mul` — `μ(m₁)μ(m₂) = μ(n)` for `n = m₁m₂`, under exact coprimality
  (squarefreeness of the two factors is *not* needed for this identity, only coprimality; the
  squarefree support is where the opening of §3 of the arithmetic bank lives).
* §3  `bdiag_reduced_conductor` — the gcd reduction `d_c = (N,e)`, `q_c = 2eb/d_c`.
* §4  `bdiag_delta_contraction_conditional` — the contraction, **conditional** on explicit
  analytic hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open Erdos287.NormalForm3221

namespace Erdos287
namespace BDiagonal

/-! ## §1  The CRT phase combination -/

/-- A literal inverse relation gives a unit. -/
theorem isCoprime_of_dvd_mul_sub_one {m c t : ℤ} (h : m ∣ c * t - 1) : IsCoprime c m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨t, -k, by linarith [hk]⟩

/-- **`bdiag_crt_inverse_congr`.**  `LEAN_PROVED` (unconditional).

Let `c = 2eb`, let `x₁` be an inverse of `c·m₂` modulo `m₁`, `x₂` an inverse of `c·m₁` modulo
`m₂`, and `z` an inverse of `c` modulo `m₁m₂`.  Then

```
x₁ m₂ + x₂ m₁  ≡  z   (mod m₁ m₂).
```

This is the exact algebraic collapse underlying the phase identity. -/
theorem bdiag_crt_inverse_congr {m1 m2 c x1 x2 z : ℤ} (hcop : IsCoprime m1 m2)
    (hx1 : m1 ∣ c * m2 * x1 - 1) (hx2 : m2 ∣ c * m1 * x2 - 1) (hz : m1 * m2 ∣ c * z - 1) :
    m1 * m2 ∣ (x1 * m2 + x2 * m1) - z := by
  have hz1 : m1 ∣ c * z - 1 := dvd_trans ⟨m2, rfl⟩ hz
  have hz2 : m2 ∣ c * z - 1 := dvd_trans ⟨m1, mul_comm m1 m2⟩ hz
  have hc1 : IsCoprime m1 c := (isCoprime_of_dvd_mul_sub_one (t := m2 * x1)
    (by simpa [mul_assoc] using hx1)).symm
  have hc2 : IsCoprime m2 c := (isCoprime_of_dvd_mul_sub_one (t := m1 * x2)
    (by simpa [mul_assoc] using hx2)).symm
  have hd1 : m1 ∣ (x1 * m2 + x2 * m1) - z := by
    refine hc1.dvd_of_dvd_mul_left ?_
    have hEq : c * ((x1 * m2 + x2 * m1) - z)
        = (c * m2 * x1 - 1) - (c * z - 1) + m1 * (c * x2) := by ring
    rw [hEq]
    exact dvd_add (dvd_sub hx1 hz1) ⟨c * x2, rfl⟩
  have hd2 : m2 ∣ (x1 * m2 + x2 * m1) - z := by
    refine hc2.dvd_of_dvd_mul_left ?_
    have hEq : c * ((x1 * m2 + x2 * m1) - z)
        = (c * m1 * x2 - 1) - (c * z - 1) + m2 * (c * x1) := by ring
    rw [hEq]
    exact dvd_add (dvd_sub hx2 hz2) ⟨c * x1, rfl⟩
  exact hcop.mul_dvd hd1 hd2

/-- **`bdiag_phase_product_modulus`.**  `LEAN_PROVED` (unconditional).

The CRT phase combination in the repository's modular-exponential representation:

```
e_{m₁}( X x₁ ) · e_{m₂}( X x₂ )  =  e_{m₁m₂}( X z ),
```

where `x₁ (2ebm₂) ≡ 1 (mod m₁)`, `x₂ (2ebm₁) ≡ 1 (mod m₂)`, `z (2eb) ≡ 1 (mod m₁m₂)`.
Writing `c = 2eb` this is exactly

```
e_{m₁}( X (2ebm₂)⁻¹ ) e_{m₂}( X (2ebm₁)⁻¹ )  =  e_{m₁m₂}( X (2eb)⁻¹ ).
```

No inverse is postulated: the hypotheses are the literal divisibilities. -/
theorem bdiag_phase_product_modulus {m1 m2 c x1 x2 z X : ℤ} (hcop : IsCoprime m1 m2)
    (hm1 : ((m1 : ℝ)) ≠ 0) (hm2 : ((m2 : ℝ)) ≠ 0)
    (hx1 : m1 ∣ c * m2 * x1 - 1) (hx2 : m2 ∣ c * m1 * x2 - 1) (hz : m1 * m2 ∣ c * z - 1) :
    phase (((X * x1 : ℤ) : ℝ) / (m1 : ℝ)) * phase (((X * x2 : ℤ) : ℝ) / (m2 : ℝ))
      = phase (((X * z : ℤ) : ℝ) / ((m1 : ℝ) * (m2 : ℝ))) := by
  rw [Erdos287.LevelPairReciprocal.reciprocal_normalForm_of_inverse hm1 hm2 X x1 x2]
  obtain ⟨k, hk⟩ := bdiag_crt_inverse_congr hcop hx1 hx2 hz
  refine Erdos287.NormalForm3221.phase_congr (X * k) ?_
  have hkR : ((x1 : ℝ) * (m2 : ℝ) + (x2 : ℝ) * (m1 : ℝ)) - (z : ℝ)
      = (m1 : ℝ) * (m2 : ℝ) * (k : ℝ) := by exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) hk
  push_cast
  field_simp
  linear_combination (X : ℝ) * hkR

/-! ## §2  The product modulus and the Möbius factor -/

/-- **`bdiag_moebius_mul`.**  `LEAN_PROVED` (unconditional).

With `n = m₁m₂` and `gcd(m₁,m₂) = 1`, `μ(m₁)μ(m₂) = μ(n)`.  Reuses Mathlib's multiplicativity
of `μ`; the banked level-pair version `moebius_levelPair_eq_moebius_n` is the same statement
with a shared `g₀` factor and is re-exported below. -/
theorem bdiag_moebius_mul {m1 m2 n : ℕ} (hcop : Nat.Coprime m1 m2) (hn : n = m1 * m2) :
    (moebius m1 : ℤ) * (moebius m2 : ℤ) = (moebius n : ℤ) := by
  rw [hn]
  exact (isMultiplicative_moebius.map_mul_of_coprime hcop).symm

/-- Re-export of the banked shared-`g₀` version; nothing is duplicated. -/
theorem bdiag_moebius_levelPair {g0 r1 r2 : ℕ} (hg0 : Squarefree g0)
    (h1 : Nat.Coprime g0 r1) (h2 : Nat.Coprime g0 r2) (hr : Nat.Coprime r1 r2) :
    (moebius (g0 * r1) : ℤ) * (moebius (g0 * r2) : ℤ) = (moebius (r1 * r2) : ℤ) :=
  Erdos287.LevelPairProduct.moebius_levelPair_eq_moebius_n hg0 h1 h2 hr

/-- **Squarefree support.**  `LEAN_PROVED`.  If `n = m₁m₂` is squarefree then so are the two
factors and they are coprime — the exact hypotheses under which `μ(m₁)μ(m₂) = μ(n)` is used. -/
theorem bdiag_squarefree_split {m1 m2 n : ℕ} (hn : n = m1 * m2) (hsq : Squarefree n) :
    Squarefree m1 ∧ Squarefree m2 ∧ Nat.Coprime m1 m2 ∧
      (moebius m1 : ℤ) * (moebius m2 : ℤ) = (moebius n : ℤ) := by
  subst hn
  obtain ⟨hcop, h1, h2⟩ := Nat.squarefree_mul_iff.mp hsq
  exact ⟨h1, h2, hcop, bdiag_moebius_mul hcop rfl⟩

/-! ## §3  The gcd reduction `d_c = (N,e)`, `q_c = 2eb/d_c` -/

/-- The reduced conductor `q_c = 2eb/d_c`, written without division: `d_c ∣ e`, so
`q_c = 2·(e/d_c)·b`. -/
def reducedConductor (N e b : ℕ) : ℕ := 2 * (e / Nat.gcd N e) * b

/-- **`bdiag_reduced_conductor`.**  `LEAN_PROVED` (unconditional).

With `d_c = gcd(N,e)` and `q_c = 2eb/d_c`:

* `d_c ∣ N` and `d_c ∣ e`;
* `d_c · q_c = 2 e b` (so the division defining `q_c` is exact);
* `gcd(N/d_c, e/d_c) = 1` — the reduced pair is primitive. -/
theorem bdiag_reduced_conductor (N e b : ℕ) (he : 0 < e) :
    Nat.gcd N e ∣ N ∧ Nat.gcd N e ∣ e ∧
      Nat.gcd N e * reducedConductor N e b = 2 * e * b ∧
      Nat.Coprime (N / Nat.gcd N e) (e / Nat.gcd N e) := by
  have hdN : Nat.gcd N e ∣ N := Nat.gcd_dvd_left N e
  have hde : Nat.gcd N e ∣ e := Nat.gcd_dvd_right N e
  have hgpos : 0 < Nat.gcd N e := Nat.gcd_pos_of_pos_right N he
  refine ⟨hdN, hde, ?_, Nat.coprime_div_gcd_div_gcd hgpos⟩
  unfold reducedConductor
  have hdiv : Nat.gcd N e * (e / Nat.gcd N e) = e := Nat.mul_div_cancel' hde
  calc Nat.gcd N e * (2 * (e / Nat.gcd N e) * b)
      = 2 * (Nat.gcd N e * (e / Nat.gcd N e)) * b := by ring
    _ = 2 * e * b := by rw [hdiv]

/-- **Unit condition transported to the reduced conductor.**  `LEAN_PROVED`.

If `u` is a unit modulo `2eb`, it is a unit modulo the reduced conductor `q_c`, because
`q_c ∣ 2eb`. -/
theorem bdiag_reduced_unit {N e b : ℕ} {u : ℤ} (he : 0 < e)
    (hu : IsCoprime u ((2 * e * b : ℕ) : ℤ)) :
    IsCoprime u ((reducedConductor N e b : ℕ) : ℤ) := by
  have hdvd : (reducedConductor N e b) ∣ 2 * e * b := by
    refine ⟨Nat.gcd N e, ?_⟩
    have h := (bdiag_reduced_conductor N e b he).2.2.1
    rw [mul_comm] at h
    exact h.symm
  have hZ : ((reducedConductor N e b : ℕ) : ℤ) ∣ ((2 * e * b : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  exact IsCoprime.of_isCoprime_of_dvd_right hu hZ

/-! ## §4  The `Δ`-large-sieve contraction — CONDITIONAL -/

/-- **`bdiag_delta_contraction_conditional`.**  `LEAN_PROVED` **conditionally**.

The claimed b-diagonal `Δ`-large-sieve contraction is **not** available unconditionally in this
repository: its analytic inputs (separated-frequency large sieve at the product modulus, and the
Archimedean packet expansion) are not formalised anywhere here.  They are therefore exposed as
explicit hypotheses, exactly as for Hybrid 2, and the compiler below is the elementary algebra
that turns them into the contraction statement.

Hypotheses:

```
hArchB    :  Btot² ≤ CarchB² · EtotB;
hPacketB  :  EtotB ≤ LB² · WsepB;
hLSB      :  WsepB ≤ 1/D + 1/M + 1/Q + Q/(D M).
```

Conclusion: `Btot ≤ η₁(CarchB, LB, D, M, Q)`.  Nothing here is unconditional. -/
theorem bdiag_delta_contraction_conditional {CarchB LB D M Q Btot EtotB WsepB : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hQ : 0 < Q)
    (hCarchB : 0 ≤ CarchB) (hLB : 0 ≤ LB)
    (hArchB : Btot ^ 2 ≤ CarchB ^ 2 * EtotB)
    (hPacketB : EtotB ≤ LB ^ 2 * WsepB)
    (hLSB : WsepB ≤ 1 / D + 1 / M + 1 / Q + Q / (D * M)) :
    Btot ≤ Erdos287.Hybrid2.eta1 CarchB LB D M Q :=
  Erdos287.Hybrid2.hybrid2_bound hD hM hQ hCarchB hLB hArchB hPacketB hLSB

/-- **The b-diagonal rectangle inherits the same firewall.**  `LEAN_PROVED`.

If the b-diagonal budget fails to contract, the survivor lies in the union of the three short
edges and the rectangle — and, exactly as in Hybrid 2, the rectangle alone does not capture the
survivor set. -/
theorem bdiag_survivor_union {C L D M Q : ℝ} (hD : 0 < D) (hM : 0 < M) (hQ : 0 < Q)
    (h : Erdos287.Hybrid2.Hybrid2Survivor C L D M Q) :
    Erdos287.Hybrid2.ShortD C L D ∨ Erdos287.Hybrid2.ShortM C L M ∨
      Erdos287.Hybrid2.ShortQ C L Q ∨ Erdos287.Hybrid2.LongEdgeRectangle C L D M Q :=
  Erdos287.Hybrid2.hybrid2_survivor_union hD hM hQ h

end BDiagonal
end Erdos287
