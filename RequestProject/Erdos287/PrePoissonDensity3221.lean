import Mathlib
import RequestProject.Erdos287.Exponent3221Ledger
import RequestProject.Erdos287.BalancedSeven3221Grouping

/-!
# V19, Phases B/E/F — the pre-Poisson affine divisor identity and the divisor-density compiler

`3221-PREPOISSON-AFFINE-DIVISOR-IDENTITY45 : LEAN_PROVED`
`3221-PREPOISSON-DIVISOR-DENSITY45 : LEAN_PROVED_FINITE`
`3221-SECONDCOPY-DENSITY45 : LEAN_PROVED_FINITE`
`3221-PREPOISSON-EXPONENT-LEDGER45 : PROVED_ALGEBRAIC / CAPACITY_ONLY`

This file is **entirely elementary**: exact residue algebra over `ℤ`, exact divisor and
interval counting over `ℤ`/`ℕ`, and exact rational arithmetic.  No analytic estimate is
proved, assumed or implied here, and nothing in this file bounds any character sum,
Kloosterman sum or exponential sum.

## What is proved

* **§A. Affine residue algebra.**  For odd `q`, `s ∈ {−1, +1}` and an affine residue `a`
  with `2a ≡ −s (mod q)`,

  `m w ≡ a (mod q)  ↔  q ∣ 2 m w + s`.

  (`affineResidue_iff_dvd_two_mul_add`, `balancedSeven_affine_divisor_condition`.)  This is
  the load-bearing pre-Poisson identity: the sampling condition is a *divisibility*
  condition on the single integer `2 m w + s`.

* **§B. Divisor density.**  Consequently, for fixed `(m, w)` with `2 m w + s ≠ 0`, *any*
  finite family of admissible moduli — in any interval whatsoever — injects into the
  divisors of `|2 m w + s|` (`sampled_q_card_le_divisorCount`,
  `sampled_q_card_le_divisorCount_affine`).  **No `τ(n) = X^{o(1)}` is proved or assumed**;
  the asymptotic divisor bound is exposed separately as an arithmetic input
  (`DivisorGrowthInput`, never inhabited here).

* **§C. Second-copy density.**  The exact interval-congruence count
  `q · #{x ∈ [a, b) : x ≡ r (mod q)} ≤ (b − a) + q`, with the floor variant
  `# ≤ 1 + (b − a) / q` (`congruence_interval_card_le`,
  `congruence_interval_card_le_one_add_quotient`,
  `secondCopy_card_le_one_add_quotient`), together with the shell description
  `w₂ = w₁ − q t` (`secondCopy_shell_iff`).

* **§D. The finite density compiler.**  `sampledQuadBox_card_le`:

  `#{(m, w₁, q, w₂)} ≤ (#m)(#w₁) · divisorMultiplicity · secondCopyMultiplicity`,

  with **no `X`-exponent anywhere inside the statement**.

* **§E/§F. The exponent ledger,** kept strictly separate from §D and reusing the V17
  `Erdos287.Ledger3221` exponents unchanged: `10/35 + 25/35 + 4/35 = 39/35`,
  `21/35 + 10/35 = 31/35`, `21/35 + 10/35 + 8/35 = 39/35`, plus the rational arithmetic
  attached to the two external capacity audits of the retired Kloosterman-fraction lane.

**Honesty statement.**  Erdős #287 remains OPEN.  Balanced7 remains OPEN.  Nothing here is
an analytic theorem, and no interface is inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open scoped Classical

namespace Erdos287
namespace PrePoisson3221

/-! ## §A. Affine residue algebra

For odd `q` the element `2` is a unit modulo `q`, so the affine residue
`a_s ≡ −s · 2⁻¹ (mod q)` is well defined; the sampling congruence `m w ≡ a_s` is then
*exactly* a divisibility statement about the single integer `2 m w + s`. -/

/-- For odd `q : ℤ`, `q` and `2` are coprime. -/
theorem isCoprime_two_of_odd {q : ℤ} (hq : Odd q) : IsCoprime q 2 := by
  obtain ⟨k, hk⟩ := hq
  exact ⟨1, -k, by linarith [hk]⟩

/-- **The pre-Poisson affine residue identity.**  `LEAN_PROVED`.

Let `q` be odd, let `s` be arbitrary, and let `a` be an affine residue for `s`, i.e.
`2 a ≡ −s (mod q)` (for odd `q` this determines `a` modulo `q`, namely `a ≡ −s·2⁻¹`).
Then for all integers `m, w`,

`m w ≡ a (mod q)  ↔  q ∣ 2 m w + s`. -/
theorem affineResidue_iff_dvd_two_mul_add {q : ℤ} (hq : Odd q) {s a m w : ℤ}
    (ha : 2 * a ≡ -s [ZMOD q]) :
    m * w ≡ a [ZMOD q] ↔ q ∣ 2 * (m * w) + s := by
  constructor
  · intro h
    have h2 : 2 * (m * w) ≡ -s [ZMOD q] := (h.mul_left 2).trans ha
    have hd : q ∣ -s - 2 * (m * w) := h2.dvd
    have hrw : 2 * (m * w) + s = -(-s - 2 * (m * w)) := by ring
    rw [hrw]
    exact dvd_neg.mpr hd
  · intro h
    have hb : q ∣ 2 * a + s := by
      have hd : q ∣ -s - 2 * a := ha.dvd
      have hrw : 2 * a + s = -(-s - 2 * a) := by ring
      rw [hrw]
      exact dvd_neg.mpr hd
    have h2 : q ∣ 2 * (m * w - a) := by
      have hrw : 2 * (m * w - a) = (2 * (m * w) + s) - (2 * a + s) := by ring
      rw [hrw]
      exact dvd_sub h hb
    have hcop : IsCoprime q 2 := isCoprime_two_of_odd hq
    have hd : q ∣ m * w - a := hcop.dvd_of_dvd_mul_left h2
    refine Int.modEq_iff_dvd.mpr ?_
    have hrw : a - m * w = -(m * w - a) := by ring
    rw [hrw]
    exact dvd_neg.mpr hd

/-- The affine residue attached to a sign `s` and an odd modulus `q`, in the form actually
used by the balanced-seven source: the sampling condition on the pair `(m, w)`. -/
def AffineSampled (q s m w : ℤ) : Prop := q ∣ 2 * (m * w) + s

/-- **`balancedSeven_affine_divisor_condition`.**  `LEAN_PROVED`.

Specialisation of `affineResidue_iff_dvd_two_mul_add` to the two admissible signs
`s = ±1` of the balanced-seven source: for odd `q`, the affine sampling congruence is
literally the divisibility `q ∣ 2 m w + s`. -/
theorem balancedSeven_affine_divisor_condition {q : ℤ} (hq : Odd q) {s : ℤ}
    (hs : s = 1 ∨ s = -1) {a m w : ℤ} (ha : 2 * a ≡ -s [ZMOD q]) :
    (m * w ≡ a [ZMOD q] ↔ AffineSampled q s m w) := by
  have := hs
  exact affineResidue_iff_dvd_two_mul_add hq ha

/-- An affine residue always exists for odd `q`: `a = −s · 2⁻¹` is realised by an explicit
integer, so the interface of §A is non-vacuous. -/
theorem exists_affineResidue {q : ℤ} (hq : Odd q) (s : ℤ) :
    ∃ a : ℤ, 2 * a ≡ -s [ZMOD q] := by
  obtain ⟨k, hk⟩ := hq
  refine ⟨-s * (k + 1), Int.modEq_iff_dvd.mpr ⟨s, ?_⟩⟩
  rw [hk]; ring

/-! ## §B. Pre-Poisson divisor density

Because the sampling condition is `q ∣ 2 m w + s`, for *fixed* `(m, w)` the admissible
moduli are divisors of one fixed nonzero integer.  Hence they are at most `τ` many, in any
interval whatsoever — the interval plays no role. -/

/-- **`sampled_q_card_le_divisorCount`.**  `LEAN_PROVED_FINITE`.

Any finite family of natural moduli all dividing a fixed nonzero integer `n` has
cardinality at most `τ(|n|)`.  No interval hypothesis is needed: the bound holds for an
arbitrary finite family, hence in particular for the family cut out by any interval. -/
theorem sampled_q_card_le_divisorCount {n : ℤ} (hn : n ≠ 0) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, (q : ℤ) ∣ n) : Q.card ≤ n.natAbs.divisors.card := by
  refine Finset.card_le_card ?_
  intro q hq
  refine Nat.mem_divisors.mpr ⟨?_, Int.natAbs_ne_zero.mpr hn⟩
  have := Int.natAbs_dvd_natAbs.mpr (hQ q hq)
  simpa using this

/-- **The affine form of the divisor-density bound.**  `LEAN_PROVED_FINITE`.

For fixed `m, w` and a sign `s` with `2 m w + s ≠ 0`, every finite family of admissible
moduli — that is, moduli satisfying the affine sampling condition — has cardinality at
most `τ(|2 m w + s|)`. -/
theorem sampled_q_card_le_divisorCount_affine {s m w : ℤ} (hne : 2 * (m * w) + s ≠ 0)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, AffineSampled (q : ℤ) s m w) :
    Q.card ≤ (2 * (m * w) + s).natAbs.divisors.card :=
  sampled_q_card_le_divisorCount hne Q hQ

/-- **`DivisorGrowthInput` — the arithmetic input, exposed separately and never inhabited
here.**

The statement `τ(n) ≤ n^ε` for all `n ≥ n₀` is a genuine (classical, but unformalised in
this repository) arithmetic theorem.  It is *not* proved above, and no result in this file
depends on it.  It is isolated here so that any later use is visible. -/
structure DivisorGrowthInput (eps : ℝ) (n₀ : ℕ) : Prop where
  /-- Positivity of the exponent. -/
  eps_pos : 0 < eps
  /-- The divisor bound in the stated range. -/
  bound : ∀ n : ℕ, n₀ ≤ n → (n.divisors.card : ℝ) ≤ (n : ℝ) ^ eps

/-! ## §C. Second-copy density: the exact interval-congruence count

The second copy of the source is sampled through the shell `w₂ = w₁ − q t`.  Over a finite
integer box this is a pure counting statement, proved here exactly — no real interval
arithmetic is used anywhere. -/

/-- The elements of `[a, b)` lying in the residue class of `r` modulo `q`. -/
noncomputable def congruenceSlice (q r a b : ℤ) : Finset ℤ :=
  (Finset.Ico a b).filter (fun x => q ∣ x - r)

/-- **The shell description.**  `w₂` lies in the class of `w₁` modulo `q` exactly when
`w₂ = w₁ − q t` for some integer `t`. -/
theorem secondCopy_shell_iff (q w₁ w₂ : ℤ) : q ∣ w₁ - w₂ ↔ ∃ t : ℤ, w₂ = w₁ - q * t := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by linarith [ht]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by ring⟩

/-- **`congruence_interval_card_le`.**  `LEAN_PROVED_FINITE`.

The exact (division-free) form of the interval-congruence count:

`q · #{x ∈ [a, b) : x ≡ r (mod q)} ≤ (b − a) + q`. -/
theorem congruence_interval_card_le {q : ℤ} (hq : 0 < q) {a b : ℤ} (hab : a ≤ b) (r : ℤ) :
    q * ((congruenceSlice q r a b).card : ℤ) ≤ (b - a) + q := by
  set al : ℤ := -((r - a) / q) with hal
  set be : ℤ := (b - 1 - r) / q with hbe
  have hmem : ∀ x ∈ congruenceSlice q r a b, (x - r) / q ∈ Finset.Ico al (be + 1) := by
    intro x hx
    simp only [congruenceSlice, Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨hxa, hxb⟩, hdvd⟩ := hx
    have hk : (x - r) / q * q = x - r := Int.ediv_mul_cancel hdvd
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · rw [hal, neg_le]
      refine (Int.le_ediv_iff_mul_le hq).mpr ?_
      have hrw : -((x - r) / q) * q = r - x := by rw [neg_mul, hk]; ring
      rw [hrw]; linarith
    · have hle : (x - r) / q ≤ be := by
        rw [hbe]
        refine (Int.le_ediv_iff_mul_le hq).mpr ?_
        rw [hk]; linarith
      omega
  have hinj : Set.InjOn (fun x => (x - r) / q) (congruenceSlice q r a b) := by
    intro x hx y hy hxy
    simp only [congruenceSlice, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    have hkx : (x - r) / q * q = x - r := Int.ediv_mul_cancel hx.2
    have hky : (y - r) / q * q = y - r := Int.ediv_mul_cancel hy.2
    simp only at hxy
    have hxy2 : x - r = y - r := by rw [← hkx, ← hky, hxy]
    linarith
  have hcard : (congruenceSlice q r a b).card ≤ (Finset.Ico al (be + 1)).card :=
    Finset.card_le_card_of_injOn _ hmem hinj
  rw [Int.card_Ico] at hcard
  have hbe_le : be * q ≤ b - 1 - r := (Int.le_ediv_iff_mul_le hq).mp hbe.le
  have hal_ge : a - r ≤ al * q := by
    have h1 : (r - a) / q * q ≤ r - a := (Int.le_ediv_iff_mul_le hq).mp le_rfl
    rw [hal, neg_mul]
    linarith
  have hgap : q * (be - al) ≤ b - 1 - a := by
    have hrw : q * (be - al) = be * q - al * q := by ring
    rw [hrw]; linarith
  rcases le_or_gt (be + 1 - al) 0 with hle | hlt
  · have hz : (be + 1 - al).toNat = 0 := Int.toNat_eq_zero.mpr hle
    rw [hz] at hcard
    have hc0 : (congruenceSlice q r a b).card = 0 := Nat.le_zero.mp hcard
    rw [hc0]
    simp only [Nat.cast_zero, mul_zero]
    linarith
  · have htn : ((be + 1 - al).toNat : ℤ) = be + 1 - al := Int.toNat_of_nonneg hlt.le
    have hc : ((congruenceSlice q r a b).card : ℤ) ≤ be + 1 - al := by
      rw [← htn]; exact_mod_cast hcard
    have h1 : q * ((congruenceSlice q r a b).card : ℤ) ≤ q * (be + 1 - al) :=
      mul_le_mul_of_nonneg_left hc hq.le
    have h2 : q * (be + 1 - al) = q * (be - al) + q := by ring
    linarith

/-- **The floor variant.**  `# ≤ 1 + (b − a) / q`, with `/` the integer (floor) division. -/
theorem congruence_interval_card_le_one_add_quotient {q : ℤ} (hq : 0 < q) {a b : ℤ}
    (hab : a ≤ b) (r : ℤ) :
    ((congruenceSlice q r a b).card : ℤ) ≤ 1 + (b - a) / q := by
  have h := congruence_interval_card_le hq hab r
  have hkey : ((congruenceSlice q r a b).card : ℤ) - 1 ≤ (b - a) / q := by
    refine (Int.le_ediv_iff_mul_le hq).mpr ?_
    have e : (((congruenceSlice q r a b).card : ℤ) - 1) * q
        = q * ((congruenceSlice q r a b).card : ℤ) - q := by ring
    rw [e]; linarith
  linarith

/-- **`secondCopy_card_le_one_add_quotient`.**  `LEAN_PROVED_FINITE`.

The second-copy count: the number of `w₂` in the box `[a, b)` for which the shell
`w₂ = w₁ − q t` is solvable is at most `1 + (b − a)/q`. -/
theorem secondCopy_card_le_one_add_quotient {q : ℤ} (hq : 0 < q) {a b : ℤ} (hab : a ≤ b)
    (w₁ : ℤ) :
    (((Finset.Ico a b).filter (fun w₂ => ∃ t : ℤ, w₂ = w₁ - q * t)).card : ℤ)
      ≤ 1 + (b - a) / q := by
  classical
  have hsub : ((Finset.Ico a b).filter (fun w₂ => ∃ t : ℤ, w₂ = w₁ - q * t))
      ⊆ congruenceSlice q w₁ a b := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    simp only [congruenceSlice, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨hx.1, ?_⟩
    obtain ⟨t, ht⟩ := hx.2
    exact ⟨-t, by rw [ht]; ring⟩
  calc (((Finset.Ico a b).filter (fun w₂ => ∃ t : ℤ, w₂ = w₁ - q * t)).card : ℤ)
      ≤ ((congruenceSlice q w₁ a b).card : ℤ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 1 + (b - a) / q := congruence_interval_card_le_one_add_quotient hq hab w₁

/-! ## §D. The finite density compiler

The two multiplicity bounds of §B and §C combine into a single finite counting statement.
There is deliberately **no `X`-exponent inside this theorem**: the exponent bookkeeping is
kept in §E, where it is exact rational arithmetic and nothing else. -/

/-- The finite box of sampled quadruples `(m, w₁, q, w₂)`. -/
def sampledQuadBox (Mset W1set : Finset ℤ) (Qsel : ℤ → ℤ → Finset ℕ)
    (W2sel : ℤ → ℤ → ℕ → Finset ℤ) : Finset (ℤ × ℤ × ℕ × ℤ) :=
  Mset.biUnion fun m => W1set.biUnion fun w1 =>
    (Qsel m w1).biUnion fun q => (W2sel m w1 q).image fun w2 => (m, w1, q, w2)

/-- **`sampledQuadBox_card_le`.**  `LEAN_PROVED_FINITE`.

The combined density count:

`#{(m, w₁, q, w₂)} ≤ (#m) · (#w₁) · divisorMultiplicity · secondCopyMultiplicity`. -/
theorem sampledQuadBox_card_le {Mset W1set : Finset ℤ} {Qsel : ℤ → ℤ → Finset ℕ}
    {W2sel : ℤ → ℤ → ℕ → Finset ℤ} {D K : ℕ}
    (hD : ∀ m ∈ Mset, ∀ w1 ∈ W1set, (Qsel m w1).card ≤ D)
    (hK : ∀ m ∈ Mset, ∀ w1 ∈ W1set, ∀ q ∈ Qsel m w1, (W2sel m w1 q).card ≤ K) :
    (sampledQuadBox Mset W1set Qsel W2sel).card ≤ Mset.card * W1set.card * D * K := by
  classical
  have inner : ∀ m ∈ Mset, ∀ w1 ∈ W1set,
      ((Qsel m w1).biUnion fun q => (W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card
        ≤ D * K := by
    intro m hm w1 hw1
    calc ((Qsel m w1).biUnion fun q => (W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card
        ≤ ∑ q ∈ Qsel m w1, ((W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ Qsel m w1, K := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact le_trans Finset.card_image_le (hK m hm w1 hw1 q hq)
      _ = (Qsel m w1).card * K := by simp [Finset.sum_const]
      _ ≤ D * K := Nat.mul_le_mul_right _ (hD m hm w1 hw1)
  calc (sampledQuadBox Mset W1set Qsel W2sel).card
      ≤ ∑ m ∈ Mset, (W1set.biUnion fun w1 =>
          (Qsel m w1).biUnion fun q => (W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ Mset, W1set.card * (D * K) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        calc (W1set.biUnion fun w1 =>
              (Qsel m w1).biUnion fun q => (W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card
            ≤ ∑ w1 ∈ W1set, ((Qsel m w1).biUnion fun q =>
                (W2sel m w1 q).image fun w2 => (m, w1, q, w2)).card := Finset.card_biUnion_le
          _ ≤ ∑ _w1 ∈ W1set, D * K := Finset.sum_le_sum fun w1 hw1 => inner m hm w1 hw1
          _ = W1set.card * (D * K) := by simp [Finset.sum_const]
    _ = Mset.card * (W1set.card * (D * K)) := by simp [Finset.sum_const]
    _ = Mset.card * W1set.card * D * K := by ring

/-! ## §E. The exponent ledger — exact rational arithmetic, `CAPACITY_ONLY`

The V17 exponents `Erdos287.Ledger3221.*` are reused unchanged.  Recall
`Eexp = 1/7`, `Mexp = Nexp = Lexp = 2/7`, `Qexp = 3/5`,
`Wexp = Eexp + Nexp + Lexp = 5/7` (the `W₅ = E N L` scale) and
`Texp = Wexp − Qexp = 4/35`.

**Nothing below is an analytic statement.**  These are rational identities recording the
internal consistency of the parameter choice, and nothing more. -/

open Erdos287.Ledger3221

/-- `M = X^{2/7} = X^{10/35}`. -/
theorem Mexp_thirtyfifths : Mexp = 10 / 35 := by norm_num [Mexp]

/-- `W₅ = E N L = X^{5/7} = X^{25/35}`. -/
theorem Wexp_thirtyfifths : Wexp = 25 / 35 := by
  norm_num [Wexp, Eexp, Nexp, Lexp]

/-- `T = W₅ / Q = X^{4/35}`. -/
theorem Texp_thirtyfifths : Texp = 4 / 35 := by
  norm_num [Texp, Wexp, Eexp, Nexp, Lexp, Qexp]

/-- `Q = X^{3/5} = X^{21/35}`. -/
theorem Qexp_thirtyfifths : Qexp = 21 / 35 := by norm_num [Qexp]

/-- The bare fraction identity `10/35 + 25/35 + 4/35 = 39/35`. -/
theorem thirtyfifths_sum : (10 : ℚ) / 35 + 25 / 35 + 4 / 35 = 39 / 35 := by norm_num

/-- **`prePoisson_density_exponent`.**  `PROVED_ALGEBRAIC / CAPACITY_ONLY`.

The pre-Poisson divisor-density count has natural exponent `M · W₅ · T = X^{39/35}`. -/
theorem prePoisson_density_exponent : Mexp + Wexp + Texp = 39 / 35 := by
  norm_num [Mexp, Wexp, Texp, Eexp, Nexp, Lexp, Qexp]

/-- **`cauchy_prefactor_exponent`.**  `PROVED_ALGEBRAIC / CAPACITY_ONLY`.

The first-Cauchy prefactor scale `Q M = X^{31/35}`. -/
theorem cauchy_prefactor_exponent : Qexp + Mexp = 31 / 35 := by
  norm_num [Qexp, Mexp]

/-- **`highCond_naturalScale_exponent`.**  `PROVED_ALGEBRAIC / CAPACITY_ONLY`.

The high-conductor natural scale `Q M T² = X^{39/35}` — the same `39/35` as the
pre-Poisson density exponent, which is exactly the capacity statement being banked. -/
theorem highCond_naturalScale_exponent : Qexp + Mexp + 2 * Texp = 39 / 35 := by
  norm_num [Qexp, Mexp, Texp, Wexp, Eexp, Nexp, Lexp]

/-- The two `39/35` routes agree: pre-Poisson density and high-conductor natural scale sit
at the *same* exponent.  `CAPACITY_ONLY` — this is a consistency check, not a saving. -/
theorem naturalScale_matches_density : Mexp + Wexp + Texp = Qexp + Mexp + 2 * Texp := by
  rw [prePoisson_density_exponent, highCond_naturalScale_exponent]

/-- `2 T = 8/35`, the doubled off-diagonal parameter exponent. -/
theorem two_Texp : 2 * Texp = 8 / 35 := by
  norm_num [Texp, Wexp, Eexp, Nexp, Lexp, Qexp]

/-! ## §F. Retired-lane capacity arithmetic — `EXTERNAL-THEOREM CAPACITY METADATA ONLY`

The Kloosterman-fraction black-box lane is **retired as the current route**.  The two
external audits attached to it are recorded here purely as *rational arithmetic*.

**These are not theorems about Bettin–Chandee or about Duke–Rudnick–Zhang, and neither of
those results is formalised, assumed, or axiomatised anywhere in this repository.  No
conclusion about the applicability or non-applicability of any external theorem may be
drawn from Lean alone.** -/

/-- **`BC3221_capacity_deficit_arithmetic`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.
The rational arithmetic `437/350 − 390/350 = 47/350 > 0`. -/
theorem BC3221_capacity_deficit_arithmetic :
    (437 : ℚ) / 350 - 390 / 350 = 47 / 350 ∧ (0 : ℚ) < 47 / 350 := by
  constructor <;> norm_num

/-- **`DRZ3221_capacity_deficit_arithmetic`.**  `PROVED_ALGEBRAIC / METADATA_ONLY`.
The rational arithmetic `523/420 − 468/420 = 11/84 > 0`. -/
theorem DRZ3221_capacity_deficit_arithmetic :
    (523 : ℚ) / 420 - 468 / 420 = 11 / 84 ∧ (0 : ℚ) < 11 / 84 := by
  constructor <;> norm_num

/-! ## §G. The labelled `1+2+2+2` source grouping, at the finite level only

The seven-prime polarization and the labelled regrouping are **already Lean-proved** in
`Erdos287.FactorialEuler` and `Erdos287.Grouping3221` and are *not* redone here.  What is
recorded below is only the finite connection to the `e / m / n / ℓ` labels used by the
pre-Poisson source, together with the scale *metadata*.

No real-power asymptotic claim is hidden in any of these finite statements. -/

/-- The labelled grouping of the pre-Poisson source, reusing the V17 grouping unchanged:
`e = p₀`, `m = p₁p₂`, `n = p₃p₄`, `ℓ = p₅p₆`, with `e·m·n·ℓ` the full product. -/
theorem prePoisson_grouping_product (p : Fin 7 → ℕ) :
    Erdos287.Grouping3221.gE p * Erdos287.Grouping3221.gM p *
      Erdos287.Grouping3221.gN p * Erdos287.Grouping3221.gL p = ∏ i, p i :=
  Erdos287.Grouping3221.grouped_product_eq p

/-- The `W₅ = E · N · L` scale, at exponent level, in the labelled grouping. -/
theorem W5_exponent_eq : Eexp + Nexp + Lexp = 5 / 7 := by
  norm_num [Eexp, Nexp, Lexp]

end PrePoisson3221
end Erdos287
