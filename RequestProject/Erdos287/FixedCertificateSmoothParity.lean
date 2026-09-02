import Mathlib
import RequestProject.Erdos287.FixedCertificateThreeError

/-!
# The smooth Möbius-parity packet (V12, Parts G3 and I)

The V12 correction makes the *smooth-parity packet* — the cell `k = 0`, `J = ∅` of the
fixed-certificate leakage census — the first literal analytic open, ahead of any H8/H9
work.  This file does three things, all finite:

1. it defines the truncated Möbius divisor weight
   `truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)` and proves its elementary properties
   (prime normalization, vanishing when the truncation is inactive);
2. it defines the interface `FixedCertificateSmoothParityPacket`, which *states* the
   claimed cell identity `H_{g*}(n) = ∑_{d ∣ n, d ≤ n^{1/2−ε}} μ(d)` on the smooth sector
   together with the claimed analytic bound, and derives the finite consequences of that
   interface (nothing here inhabits it);
3. it builds the **parent leakage interface**: the leakage over the whole region `U` is
   controlled by the sum of the child bounds, one of which is the smooth-parity packet,
   and feeds that into the three-error transference theorem.

## Honesty statement (source archaeology)

The literal Ford factorisation of `G(m;n)` — the object whose `k = 0`, `J = ∅` cell would
*prove* the identity in `cell_identity` — is **not present in this repository** (the same
gap is already recorded in `TrustedBank/R9/Certificate.lean`).  Therefore:

* the cell identity is carried as a hypothesis field of the interface, never asserted;
* the analytic estimate `ERDOS287_FIXED_CERTIFICATE_SMOOTH_PARITY45` is **OPEN**;
* the missing source theorem is named exactly in `smoothParity_missing_source` below.

## Main results

* `truncMobius_prime`, `truncMobius_one`, `truncMobius_eq_zero_of_le`;
* `smoothParity_prime_normalization` — the packet forces `H_{g*}(p) = 1` on primes above
  the truncation, i.e. it is consistent with the `P`-normalization of the transference
  theorem;
* `parent_leakage_of_children`, `parent_leakage_two_children` — the parent leakage bound
  as a sum of child bounds;
* `parent_prime_mass_pos` — all child bounds + total correlation + `N2` bound +
  comparison margin ⇒ strictly positive prime mass.
-/

open scoped BigOperators
open ArithmeticFunction

namespace Erdos287
namespace SmoothParity

/-! ## The truncated Möbius weight -/

/-- `truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)`. -/
def truncMobius (n T : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ T), moebius d

/-- At `n = 1` the weight is `1` (for any active truncation `T ≥ 1`). -/
theorem truncMobius_one {T : ℕ} (hT : 1 ≤ T) : truncMobius 1 T = 1 := by
  have hset : (1 : ℕ).divisors.filter (fun d => d ≤ T) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton,
      Nat.divisors_one, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, hT⟩
  rw [truncMobius, hset]
  simp

/-- **Prime normalization.**  For a prime `p` above the truncation, only `d = 1` survives,
so the weight is `1`. -/
theorem truncMobius_prime {p T : ℕ} (hp : p.Prime) (h1 : 1 ≤ T) (h2 : T < p) :
    truncMobius p T = 1 := by
  have hset : p.divisors.filter (fun d => d ≤ T) = {1} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hdT⟩
      rcases hp.eq_one_or_self_of_dvd d hd with h | h
      · exact h
      · omega
    · rintro rfl; exact ⟨⟨one_dvd _, hp.ne_zero⟩, h1⟩
  rw [truncMobius, hset]
  simp

/-- The full Möbius sum over all divisors vanishes for `n > 1`. -/
theorem sum_moebius_divisors_eq_zero {n : ℕ} (h : 1 < n) :
    ∑ d ∈ n.divisors, moebius d = 0 := by
  have h1 : ((moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n
      = (1 : ArithmeticFunction ℤ) n := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne (by omega)] at h1
  exact h1

/-- **Inactive truncation.**  If the cut is above `n` itself, the truncated weight is the
full Möbius sum, hence `0` for `n > 1`: the packet is genuinely about the *truncation*,
not about the divisor sum. -/
theorem truncMobius_eq_zero_of_le {n T : ℕ} (h : 1 < n) (hT : n ≤ T) :
    truncMobius n T = 0 := by
  have hset : n.divisors.filter (fun d => d ≤ T) = n.divisors := by
    refine Finset.filter_true_of_mem ?_
    intro d hd
    exact le_trans (Nat.le_of_dvd (by omega) (Nat.mem_divisors.1 hd).1) hT
  rw [truncMobius, hset]
  exact sum_moebius_divisors_eq_zero h

/-! ## The packet interface -/

/-- **`FixedCertificateSmoothParityPacket`.**  The interface for the cell `k = 0`,
`J = ∅` of the fixed-certificate leakage census.

* `cell_identity` is the *claimed* source identity: on the smooth sector the fixed
  certificate's arithmetic weight is the truncated Möbius weight at the cut `cut n`
  (in the source, `cut n = ⌊n^{1/2−ε}⌋`);
* `cut_pos` records that the cut is active;
* `analytic_bound` is the *claimed* analytic estimate
  `ERDOS287_FIXED_CERTIFICATE_SMOOTH_PARITY45`.

Nothing in this project inhabits this structure: both fields are external obligations,
the first a Gate-1B source-transcription obligation and the second an open analytic
estimate. -/
structure FixedCertificateSmoothParityPacket
    (sector : Finset ℕ) (Hs : ℕ → ℤ) (cut : ℕ → ℕ) (f : ℕ → ℝ) (E : ℝ) : Prop where
  /-- The cut is active on the sector. -/
  cut_pos : ∀ n ∈ sector, 1 ≤ cut n
  /-- The `k = 0`, `J = ∅` cell identity. -/
  cell_identity : ∀ n ∈ sector, Hs n = truncMobius n (cut n)
  /-- The analytic estimate for the packet's contribution. -/
  analytic_bound : |∑ n ∈ sector, f n * (Hs n : ℝ)| ≤ E

/-- **Prime normalization from the packet.**  If the packet holds and `p` is a prime of
the sector lying above its own cut, then `H_{g*}(p) = 1` — exactly the `P`-normalization
required by the transference theorem.  This is the finite consistency check that the
packet must pass. -/
theorem smoothParity_prime_normalization
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ} {E : ℝ}
    (h : FixedCertificateSmoothParityPacket sector Hs cut f E)
    {p : ℕ} (hp : p ∈ sector) (hprime : p.Prime) (hcut : cut p < p) :
    Hs p = 1 := by
  rw [h.cell_identity p hp]
  exact truncMobius_prime hprime (h.cut_pos p hp) hcut

/-- **Degenerate cells are annihilated.**  If the cut is inactive at a composite `n` of
the sector (cut above `n`), the packet forces the weight to vanish there.  Hence the
packet's content is concentrated on the genuinely truncated range. -/
theorem smoothParity_inactive_cut
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ} {f : ℕ → ℝ} {E : ℝ}
    (h : FixedCertificateSmoothParityPacket sector Hs cut f E)
    {n : ℕ} (hn : n ∈ sector) (h1 : 1 < n) (hcut : n ≤ cut n) :
    Hs n = 0 := by
  rw [h.cell_identity n hn]
  exact truncMobius_eq_zero_of_le h1 hcut

/-- **The exact missing source theorem.**  What has to be supplied externally, in words:
*the `k = 0`, `J = ∅` cell of the Ford factorisation of `G_{g*}(m;n)` equals the
truncated Möbius weight `∑_{d ∣ n, d ≤ n^{1/2−ε}} μ(d)` on the smooth-prime-factor
sector.*  Formally, that is precisely an inhabitant of the `cell_identity` field.  This
lemma records that the field is what is needed and nothing more: given it (and an active
cut), the identity holds pointwise. -/
theorem smoothParity_missing_source
    {sector : Finset ℕ} {Hs : ℕ → ℤ} {cut : ℕ → ℕ}
    (hcell : ∀ n ∈ sector, Hs n = truncMobius n (cut n))
    {n : ℕ} (hn : n ∈ sector) :
    Hs n = ∑ d ∈ n.divisors.filter (fun d => d ≤ cut n), moebius d :=
  hcell n hn

/-! ## The parent leakage interface (Part I) -/

/-- **Parent leakage bound.**  If the leakage region `U` is partitioned into child
packets `Uc i` and each child is bounded by `E i`, the parent leakage is bounded by
`∑ E i`.  The smooth-parity packet is one of the children; the parent estimate
`287-FIXED-CERTIFICATE-LEAKAGE45` is therefore *not* available until every child is. -/
theorem parent_leakage_of_children {κ : Type*} [DecidableEq κ]
    (U : Finset ℕ) (children : Finset κ) (Uc : κ → Finset ℕ) (E : κ → ℝ) (f : ℕ → ℝ)
    (hcover : U = children.biUnion Uc)
    (hdisj : ∀ i ∈ children, ∀ j ∈ children, i ≠ j → Disjoint (Uc i) (Uc j))
    (hchild : ∀ i ∈ children, |∑ n ∈ Uc i, f n| ≤ E i) :
    |∑ n ∈ U, f n| ≤ ∑ i ∈ children, E i := by
  rw [hcover, Finset.sum_biUnion hdisj]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum hchild

/-- The two-child form actually used: the smooth-parity packet plus everything else. -/
theorem parent_leakage_two_children
    (Usmooth Urest : Finset ℕ) (f : ℕ → ℝ) (Es Er : ℝ)
    (hdisj : Disjoint Usmooth Urest)
    (hs : |∑ n ∈ Usmooth, f n| ≤ Es)
    (hr : |∑ n ∈ Urest, f n| ≤ Er) :
    |∑ n ∈ (Usmooth ∪ Urest), f n| ≤ Es + Er := by
  rw [Finset.sum_union hdisj]
  exact le_trans (abs_add_le _ _) (add_le_add hs hr)

/-- **Parent compiler.**  All child leakage bounds, the total-correlation bound, the `N2`
bound and the comparison margin together give a strictly positive prime mass.

Every analytic input is an explicit antecedent; the smooth-parity child bound is the
antecedent `hs`, which this project does **not** prove. -/
theorem parent_prime_mass_pos
    (P N1 N2 Usmooth Urest : Finset ℕ) (a b w H : ℕ → ℝ) (Cc ET Es Er E2 EM : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P (Usmooth ∪ Urest))
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 (Usmooth ∪ Urest))
    (hN2U : Disjoint N2 (Usmooth ∪ Urest))
    (hSR : Disjoint Usmooth Urest)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ (Usmooth ∪ Urest)), w n * H n| ≤ ET)
    (hs : |∑ n ∈ Usmooth, w n * H n| ≤ Es)
    (hr : |∑ n ∈ Urest, w n * H n| ≤ Er)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n)
    (hsmall : ET + (Es + Er) + E2 + EM < (1 + Cc) * (∑ p ∈ P, b p)) :
    0 < ∑ p ∈ P, a p :=
  Transference4.sum_a_P_pos4_fraction P N1 N2 (Usmooth ∪ Urest) a b w H Cc ET (Es + Er) E2 EM
    hw ha hHP hHN1 hPN1 hPN2 hPU hN1N2 hN1U hN2U hTotal
    (parent_leakage_two_children Usmooth Urest (fun n => w n * H n) Es Er hSR hs hr)
    hN2 hMargin hsmall

end SmoothParity
end Erdos287
