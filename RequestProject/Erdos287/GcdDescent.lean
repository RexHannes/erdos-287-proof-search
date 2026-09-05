import Mathlib
import RequestProject.Erdos287.SourceWeights

/-!
# Erdős #287 — exact squarefree gcd descent

```
COPRIME MOBIUS INDICATOR         : KERNEL-PROVED   (coprime_indicator_mobius)
LOCAL COEFFICIENT IDENTITY       : KERNEL-PROVED   (local_coefficient_identity)
SQUAREFREE GCD DESCENT           : KERNEL-PROVED   (squarefree_gcd_descent)
DESCENT COPRIMALITY  gcd(b,qv)=1 : KERNEL-PROVED   (descentIndex_coprime)
ONE-PRIME SANITY CHECK           : KERNEL-PROVED   (onePrime_shared_cancellation)
PHASE DESCENT                    : KERNEL-PROVED   (phase_descent, W_argument_descent, ...)
HYPERBOLA SUPPORT DESCENT        : KERNEL-PROVED   (hyperbola_support_gcd_descent)
```

Everything here is finite divisor algebra over `ℚ`; no analytic input is used.

The source coefficient of the squarefree medium-`k` operator is

    μ(u) · B_src(u) · β(k) · 1_{gcd(u,k)=1}.

Substituting `1_{gcd(u,k)=1} = ∑_{b ∣ gcd(u,k)} μ(b)` and writing `u = b v`, `k = b q`
turns the coefficient into the *exact* descended local coefficient

    λ(b) · β(q) · μ(v) · B_src(v),          λ(b) = ∏_{p ∣ b} (p−1)/(p−2)².

Note that `gcd(q, v) = 1` is **not** available and is never used: `q` and `v` may share
primes in the descended representation, and the cancellation over `b` reconstructs the
original coprimality constraint.  What *is* available is `gcd(b, q·v) = 1`
(`descentIndex_coprime`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction Erdos287.SourceWeights

namespace Erdos287
namespace GcdDescent

/-! ## §2  The Möbius coprimality indicator -/

/-- `∑_{d ∣ n} μ(d) = [n = 1]` for `n ≠ 0`. -/
theorem sum_divisors_moebius (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal
      (f := fun x y => (ArithmeticFunction.moebius x : ℤ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) y)] at h
  rw [ArithmeticFunction.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : n / d ≠ 0 :=
    Nat.div_ne_zero_iff.2 ⟨fun h0 => hn (by simpa [h0] using hdvd),
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd⟩
  simp [hd0]

/-- **`coprime_indicator_mobius`.** `KERNEL-PROVED`.  The integer-valued coprimality
indicator as a divisor sum of the Möbius function:

    1_{gcd(u,k)=1} = ∑_{b ∣ gcd(u,k)} μ(b). -/
theorem coprime_indicator_mobius {u k : ℕ} (hu : u ≠ 0) :
    ∑ b ∈ (Nat.gcd u k).divisors, (moebius b : ℤ) = if Nat.Coprime u k then 1 else 0 := by
  have hg : Nat.gcd u k ≠ 0 := fun h => hu (Nat.eq_zero_of_gcd_eq_zero_left h)
  simpa [Nat.Coprime] using sum_divisors_moebius (Nat.gcd u k) hg

/-- The rational-valued form of the indicator. -/
theorem coprime_indicator_mobius_rat {u k : ℕ} (hu : u ≠ 0) :
    ∑ b ∈ (Nat.gcd u k).divisors, (moebius b : ℚ) = if Nat.Coprime u k then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (coprime_indicator_mobius (k := k) hu)
  simpa using h

/-! ## §3.1  The exact local coefficient identity -/

/-- **`local_coefficient_identity`.** `KERNEL-PROVED`.  For squarefree `b` coprime to both
`v` and `q`,

    μ(b) · μ(bv) · B_src(bv) · β(bq) = λ(b) · μ(v) · B_src(v) · β(q).

The two Möbius factors in `b` cancel because `μ(b)² = 1` for squarefree `b`; the surviving
`b`-local weight is `B0(b)·β(b) = λ(b)`.  Coprimality of `q` and `v` is **not** assumed. -/
theorem local_coefficient_identity (S2 : ℚ) {b q v : ℕ} (hb : Squarefree b) (hb0 : b ≠ 0)
    (hq0 : q ≠ 0) (hv0 : v ≠ 0) (hbv : Nat.Coprime b v) (hbq : Nat.Coprime b q) :
    (moebius b : ℚ) * (moebius (b * v) : ℚ) * Bsrc S2 (b * v) * beta (b * q)
      = lam b * (moebius v : ℚ) * Bsrc S2 v * beta q := by
  have hmu : (moebius (b * v) : ℚ) = (moebius b : ℚ) * (moebius v : ℚ) := by
    have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hbv
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
  have hsq : ((moebius b : ℤ) : ℚ) * ((moebius b : ℤ) : ℚ) = 1 := by
    have h : ((moebius b : ℤ) : ℚ) ^ 2 = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (moebius_sq_eq_one_of_squarefree hb)
    rw [← sq]; exact h
  have hB : Bsrc S2 (b * v) = S2 * (B0 b * B0 v) := by
    simp [Bsrc, B0_mul hb0 hv0 hbv]
  have hbeta : beta (b * q) = beta b * beta q := beta_mul hb0 hq0 hbq
  rw [hmu, hB, hbeta, lam_eq_B0_mul_beta, Bsrc]
  linear_combination ((moebius v : ℚ) * S2 * B0 b * B0 v * beta b * beta q) * hsq

/-! ## §3.2  The descent index sets -/

/-- The *original* index set: triples `(u, k, b)` with `u ∈ U`, `k ∈ K` and `b ∣ gcd(u,k)`. -/
def sourceIndex (U K : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (U ×ˢ K ×ˢ (U.biUnion Nat.divisors)).filter (fun t => t.2.2 ∣ t.1 ∧ t.2.2 ∣ t.2.1)

/-- The *descended* index set: triples `(b, q, v)` with `b·v ∈ U` and `b·q ∈ K`. -/
def descentIndex (U K : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((U.biUnion Nat.divisors) ×ˢ (K.biUnion Nat.divisors) ×ˢ (U.biUnion Nat.divisors)).filter
    (fun t => t.1 * t.2.2 ∈ U ∧ t.1 * t.2.1 ∈ K)

theorem mem_sourceIndex_iff {U K : Finset ℕ} (hU0 : 0 ∉ U) {u k b : ℕ} :
    (u, k, b) ∈ sourceIndex U K ↔ u ∈ U ∧ k ∈ K ∧ b ∣ u ∧ b ∣ k := by
  constructor
  · intro h
    rw [sourceIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at h
    exact ⟨h.1.1, h.1.2.1, h.2.1, h.2.2⟩
  · rintro ⟨hu, hk, hbu, hbk⟩
    have hu0 : u ≠ 0 := by rintro rfl; exact hU0 hu
    rw [sourceIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    exact ⟨⟨hu, hk, Finset.mem_biUnion.2 ⟨u, hu, Nat.mem_divisors.2 ⟨hbu, hu0⟩⟩⟩, hbu, hbk⟩

theorem mem_descentIndex_iff {U K : Finset ℕ} (hU0 : 0 ∉ U) (hK0 : 0 ∉ K) {b q v : ℕ} :
    (b, q, v) ∈ descentIndex U K ↔ b * v ∈ U ∧ b * q ∈ K := by
  constructor
  · intro h
    rw [descentIndex, Finset.mem_filter] at h
    exact h.2
  · rintro ⟨hbv, hbq⟩
    have hbv0 : b * v ≠ 0 := by intro h; rw [h] at hbv; exact hU0 hbv
    have hbq0 : b * q ≠ 0 := by intro h; rw [h] at hbq; exact hK0 hbq
    rw [descentIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    dsimp only
    exact ⟨⟨Finset.mem_biUnion.2 ⟨b * v, hbv, Nat.mem_divisors.2 ⟨dvd_mul_right b v, hbv0⟩⟩,
      Finset.mem_biUnion.2 ⟨b * q, hbq, Nat.mem_divisors.2 ⟨dvd_mul_left q b, hbq0⟩⟩,
      Finset.mem_biUnion.2 ⟨b * v, hbv, Nat.mem_divisors.2 ⟨dvd_mul_left v b, hbv0⟩⟩⟩,
      hbv, hbq⟩

/-- **`descentIndex_coprime`.** `KERNEL-PROVED`.  Squarefreeness of `u = bv` and `k = bq`
forces `gcd(b, v) = gcd(b, q) = 1`, hence `gcd(b, q·v) = 1`.  Note `gcd(q, v)` is
*unconstrained*. -/
theorem descentIndex_coprime {U K : Finset ℕ} (hU0 : 0 ∉ U) (hK0 : 0 ∉ K)
    (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) {b q v : ℕ}
    (h : (b, q, v) ∈ descentIndex U K) : Nat.Coprime b (q * v) := by
  obtain ⟨hbv, hbq⟩ := (mem_descentIndex_iff hU0 hK0).1 h
  have h1 : Nat.Coprime b v := (Nat.squarefree_mul_iff.1 (hUsf _ hbv)).1
  have h2 : Nat.Coprime b q := (Nat.squarefree_mul_iff.1 (hKsf _ hbq)).1
  exact Nat.Coprime.mul_right h2 h1

/-! ## §3.3  The central reindexing theorem -/

private theorem filter_biUnion_divisors_eq {U : Finset ℕ} (hU0 : 0 ∉ U) {u : ℕ} (hu : u ∈ U)
    (k : ℕ) :
    (U.biUnion Nat.divisors).filter (fun b => b ∣ u ∧ b ∣ k) = (Nat.gcd u k).divisors := by
  have hu0 : u ≠ 0 := fun h => hU0 (h ▸ hu)
  ext b
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, hbu, hbk⟩
    exact ⟨Nat.dvd_gcd hbu hbk, fun h => hu0 (Nat.eq_zero_of_gcd_eq_zero_left h)⟩
  · rintro ⟨hbg, -⟩
    have hbu : b ∣ u := hbg.trans (Nat.gcd_dvd_left u k)
    have hbk : b ∣ k := hbg.trans (Nat.gcd_dvd_right u k)
    exact ⟨⟨u, hu, hbu, hu0⟩, hbu, hbk⟩

/-- Step 1 of the descent: expand the coprimality indicator and flatten the triple sum. -/
private theorem source_sum_eq_sourceIndex_sum {R : Type*} [CommRing R] (φ : ℚ →+* R)
    (G : ℕ → ℕ → R) {U K : Finset ℕ} (hU0 : 0 ∉ U) :
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : R) else 0) * G u k
      = ∑ t ∈ sourceIndex U K, φ (moebius t.2.2 : ℚ) * G t.1 t.2.1 := by
  rw [sourceIndex, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun u hu => ?_
  conv_rhs => rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hu0 : u ≠ 0 := by rintro rfl; exact hU0 hu
  dsimp only
  rw [← Finset.sum_filter, filter_biUnion_divisors_eq hU0 hu k, ← Finset.sum_mul]
  congr 1
  rw [← map_sum φ, coprime_indicator_mobius_rat (k := k) hu0]
  split <;> simp

/-- **`squarefree_gcd_descent`.** `KERNEL-PROVED`.  The central exact reindexing:

    ∑_{u ∈ U} ∑_{k ∈ K} μ(u) B_src(u) β(k) 1_{gcd(u,k)=1} F(u,k)
      = ∑_{(b,q,v) : bv ∈ U, bq ∈ K} λ(b) β(q) μ(v) B_src(v) F(bv, bq),

for finite sets `U, K` of nonzero squarefree moduli and an arbitrary weight `F`.

The coefficients are rational; the weight `F` may take values in any commutative ring `R`
receiving `ℚ` through a ring homomorphism `φ` (in practice `R = ℚ` or `R = ℝ`). -/
theorem squarefree_gcd_descent_map {R : Type*} [CommRing R] (φ : ℚ →+* R) (S2 : ℚ)
    (F : ℕ → ℕ → R) {U K : Finset ℕ}
    (hU0 : 0 ∉ U) (hK0 : 0 ∉ K) (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) :
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : R) else 0) *
        (φ ((moebius u : ℚ) * Bsrc S2 u * beta k) * F u k)
      = ∑ t ∈ descentIndex U K,
          φ (lam t.1 * beta t.2.1 * (moebius t.2.2 : ℚ) * Bsrc S2 t.2.2) *
            F (t.1 * t.2.2) (t.1 * t.2.1) := by
  classical
  rw [source_sum_eq_sourceIndex_sum φ
    (fun u k => φ ((moebius u : ℚ) * Bsrc S2 u * beta k) * F u k) hU0]
  refine Finset.sum_nbij' (fun t => (t.2.2, t.2.1 / t.2.2, t.1 / t.2.2))
    (fun t => (t.1 * t.2.2, t.1 * t.2.1, t.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, k, b⟩ ht
    obtain ⟨hu, hk, hbu, hbk⟩ := (mem_sourceIndex_iff hU0).1 ht
    have hu0 : u ≠ 0 := fun h => hU0 (h ▸ hu)
    have hb0 : b ≠ 0 := by rintro rfl; exact hu0 (Nat.eq_zero_of_zero_dvd hbu)
    refine (mem_descentIndex_iff hU0 hK0).2 ⟨?_, ?_⟩
    · rwa [Nat.mul_div_cancel' hbu]
    · rwa [Nat.mul_div_cancel' hbk]
  · rintro ⟨b, q, v⟩ ht
    obtain ⟨hbv, hbq⟩ := (mem_descentIndex_iff hU0 hK0).1 ht
    exact (mem_sourceIndex_iff hU0).2 ⟨hbv, hbq, ⟨v, rfl⟩, ⟨q, rfl⟩⟩
  · rintro ⟨u, k, b⟩ ht
    obtain ⟨hu, hk, hbu, hbk⟩ := (mem_sourceIndex_iff hU0).1 ht
    have hu0 : u ≠ 0 := fun h => hU0 (h ▸ hu)
    have hb0 : b ≠ 0 := by rintro rfl; exact hu0 (Nat.eq_zero_of_zero_dvd hbu)
    simp [Nat.mul_div_cancel' hbu, Nat.mul_div_cancel' hbk]
  · rintro ⟨b, q, v⟩ ht
    obtain ⟨hbv, hbq⟩ := (mem_descentIndex_iff hU0 hK0).1 ht
    have hbv0 : b * v ≠ 0 := fun h => hU0 (h ▸ hbv)
    have hb0 : b ≠ 0 := by rintro rfl; exact hbv0 (by ring)
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb0)]
  · rintro ⟨u, k, b⟩ ht
    obtain ⟨hu, hk, hbu, hbk⟩ := (mem_sourceIndex_iff hU0).1 ht
    have hu0 : u ≠ 0 := fun h => hU0 (h ▸ hu)
    have hk0 : k ≠ 0 := fun h => hK0 (h ▸ hk)
    have hb0 : b ≠ 0 := by rintro rfl; exact hu0 (Nat.eq_zero_of_zero_dvd hbu)
    have husf : Squarefree u := hUsf u hu
    have hksf : Squarefree k := hKsf k hk
    set v := u / b with hv
    set q := k / b with hq
    have hue : u = b * v := (Nat.mul_div_cancel' hbu).symm
    have hke : k = b * q := (Nat.mul_div_cancel' hbk).symm
    have hv0 : v ≠ 0 := by rintro h; rw [h, mul_zero] at hue; exact hu0 hue
    have hq0 : q ≠ 0 := by rintro h; rw [h, mul_zero] at hke; exact hk0 hke
    have hsfu : Squarefree (b * v) := hue ▸ husf
    have hsfk : Squarefree (b * q) := hke ▸ hksf
    have hbv : Nat.Coprime b v := (Nat.squarefree_mul_iff.1 hsfu).1
    have hbq : Nat.Coprime b q := (Nat.squarefree_mul_iff.1 hsfk).1
    have hbsf : Squarefree b := (Nat.squarefree_mul_iff.1 hsfu).2.1
    have hcore : (moebius b : ℚ) * ((moebius (b * v) : ℚ) * Bsrc S2 (b * v) * beta (b * q))
        = lam b * beta q * (moebius v : ℚ) * Bsrc S2 v := by
      linear_combination local_coefficient_identity S2 hbsf hb0 hq0 hv0 hbv hbq
    calc φ (moebius b : ℚ) * (φ ((moebius u : ℚ) * Bsrc S2 u * beta k) * F u k)
        = φ ((moebius b : ℚ) * ((moebius (b * v) : ℚ) * Bsrc S2 (b * v) * beta (b * q)))
            * F (b * v) (b * q) := by rw [← hue, ← hke]; simp only [map_mul]; ring
      _ = φ (lam b * beta q * (moebius v : ℚ) * Bsrc S2 v) * F (b * v) (b * q) := by rw [hcore]

/-- **`squarefree_gcd_descent`.** `KERNEL-PROVED`.  The rational-coefficient instance of the
central reindexing. -/
theorem squarefree_gcd_descent (S2 : ℚ) (F : ℕ → ℕ → ℚ) {U K : Finset ℕ}
    (hU0 : 0 ∉ U) (hK0 : 0 ∉ K) (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) :
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : ℚ) else 0) *
        ((moebius u : ℚ) * Bsrc S2 u * beta k * F u k)
      = ∑ t ∈ descentIndex U K,
          lam t.1 * beta t.2.1 * (moebius t.2.2 : ℚ) * Bsrc S2 t.2.2 *
            F (t.1 * t.2.2) (t.1 * t.2.1) := by
  have h := squarefree_gcd_descent_map (RingHom.id ℚ) S2 F hU0 hK0 hUsf hKsf
  simpa only [RingHom.id_apply] using h

/-- **`squarefree_gcd_descent_real`.** `KERNEL-PROVED`.  The real-valued instance, used by the
medium-`k` normal form where `F` is built from the joint Bernoulli kernel. -/
theorem squarefree_gcd_descent_real (S2 : ℚ) (F : ℕ → ℕ → ℝ) {U K : Finset ℕ}
    (hU0 : 0 ∉ U) (hK0 : 0 ∉ K) (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) :
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : ℝ) else 0) *
        ((((moebius u : ℚ) * Bsrc S2 u * beta k : ℚ) : ℝ) * F u k)
      = ∑ t ∈ descentIndex U K,
          (((lam t.1 * beta t.2.1 * (moebius t.2.2 : ℚ) * Bsrc S2 t.2.2 : ℚ) : ℝ)) *
            F (t.1 * t.2.2) (t.1 * t.2.1) :=
  squarefree_gcd_descent_map (Rat.castHom ℝ) S2 F hU0 hK0 hUsf hKsf

/-! ## §3.4  One-prime sanity check: an illegal shared prime cancels exactly -/

/-- **`onePrime_shared_cancellation`.** `KERNEL-PROVED`.  The one-prime local state:
for `u = k = p` the two descended configurations `b = 1` and `b = p` cancel exactly, so the
descended sum reproduces the (vanishing) coprime source sum. -/
theorem onePrime_shared_cancellation {p : ℕ} (hp : p.Prime) :
    ∑ b ∈ (Nat.gcd p p).divisors, (moebius b : ℚ) = 0 := by
  rw [coprime_indicator_mobius_rat hp.pos.ne']
  have hnc : ¬ Nat.Coprime p p := by simp [Nat.Coprime, Nat.gcd_self, hp.ne_one]
  simp [hnc]

/-! ## §4  Phase / weight substitution under `u = bv`, `k = bq` -/

/-- **`phase_descent`.** `KERNEL-PROVED`.  `c·u/k = c·v/q` when `u = bv`, `k = bq`. -/
theorem phase_descent (c b q v : ℝ) (hb : b ≠ 0) (hq : q ≠ 0) :
    c * (b * v) / (b * q) = c * v / q := by
  field_simp

/-- The sawtooth (or any function) evaluated at the descended phase agrees. -/
theorem phase_descent_apply (psi : ℝ → ℝ) (c b q v : ℝ) (hb : b ≠ 0) (hq : q ≠ 0) :
    psi (c * (b * v) / (b * q)) = psi (c * v / q) := by
  rw [phase_descent c b q v hb hq]

/-- **`W_argument_descent`.** `KERNEL-PROVED`.  `(c·u)²/X = c²b²v²/X` when `u = bv`. -/
theorem W_argument_descent (c b v X : ℝ) : (c * (b * v)) ^ 2 / X = c ^ 2 * b ^ 2 * v ^ 2 / X := by
  ring

/-- **`derivative_argument_descent`.** `KERNEL-PROVED`.  `X·y/(c·k·u) = X·y/(c·b²·q·v)`. -/
theorem derivative_argument_descent (X y c b q v : ℝ) :
    X * y / (c * (b * q) * (b * v)) = X * y / (c * b ^ 2 * q * v) := by
  ring_nf

/-! ## §5  Hyperbolic support descent -/

/-- **`hyperbola_support_gcd_descent`.** `KERNEL-PROVED`.  The support condition
`k·u ≤ (9/10)·X/c` becomes `b²·q·v ≤ (9/10)·X/c` under `k = bq`, `u = bv`.
The decimal `0.9` is handled as the exact rational `9/10`. -/
theorem hyperbola_support_gcd_descent (X c b q v : ℝ) :
    (b * q) * (b * v) ≤ (9 / 10) * X / c ↔ b ^ 2 * q * v ≤ (9 / 10) * X / c := by
  constructor <;> intro h <;> [nlinarith [h]; nlinarith [h]]

/-- The natural-number form of the support descent. -/
theorem hyperbola_support_gcd_descent_nat (b q v : ℕ) : (b * q) * (b * v) = b ^ 2 * q * v := by
  ring

end GcdDescent
end Erdos287
