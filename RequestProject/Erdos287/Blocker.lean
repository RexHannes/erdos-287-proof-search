import RequestProject.Erdos287.Window
import RequestProject.Erdos287.Counterexample
import RequestProject.Erdos287.PrimeFree

/-!
# Erdős Problem #287 — reusable blocker / certificate framework

Building on the certified structural kernel (`primePower_window_exclusion`, the `C`
values, and the `Gap2CE` structure), this file packages the prime-power exclusion
argument into a small, reusable certificate/checker API:

* `ExcludedPP M q` — a reusable predicate: `q = p^e` is a prime power whose window
  numerator bound `C ⌊M/q⌋` is `< p`.  Any multiple of such a `q` is excluded from a
  reciprocal-sum-`1` set `A ⊆ [1,M]` (`ExcludedPP.not_dvd_mem`,
  `Gap2CE.notMem_of_excludedPP`).
* `Gap2CE.excludedPP_blockerPair` — the clean blocker-pair theorem: two adjacent
  excluded multiples refute a `Gap2CE`.
* `BlockerCert` — a finite, self-contained certificate structure, with
  `BlockerCert.refutes` proving that any valid certificate refutes a `Gap2CE`.
* Generalized good-prime / cofactor blockers
  (`Gap2CE.goodPrime_blocker_sub`, `Gap2CE.goodPrime_blocker_add`) and the
  safe-prime corollary (`Gap2CE.safePrime_blocker`).
* A small sound propagation layer (`Gap2CE.forced_right`, `Gap2CE.forced_left`).
-/

open scoped BigOperators

namespace Erdos287

/-! ## The excluded-prime-power predicate -/

/-- `ExcludedPP M q` : `q` is a prime power `p^e` (`e ≥ 1`) such that the largest
reciprocal-sum numerator over subsets of `{1,…,⌊M/q⌋}` is `< p`.  By
`primePower_window_exclusion`, no element of a reciprocal-sum-`1` set `A ⊆ [1,M]` is
divisible by `q`. -/
def ExcludedPP (M q : ℕ) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ q = p ^ e ∧ C (M / q) < (p : ℤ)

/-
A prime power `r^e` is excluded whenever the window numerator bound at some
`j ≥ ⌊M/r^e⌋` is below the base `r`.
-/
theorem excludedPP_of_le {M r e j : ℕ} (hr : r.Prime) (he : 1 ≤ e)
    (hj : M / r ^ e ≤ j) (hC : C j < (r : ℤ)) : ExcludedPP M (r ^ e) := by
  exact ⟨ r, e, hr, he, rfl, lt_of_le_of_lt ( C_mono hj ) hC ⟩

/-
A prime `p` with `M/2 < p ≤ M` is excluded (`q = p`, window `⌊M/p⌋ = 1`,
`C 1 = 1 < p`).
-/
theorem excludedPP_self_of_large {M p : ℕ} (hp : p.Prime) (hpM : p ≤ M)
    (hM2 : M < 2 * p) : ExcludedPP M p := by
  use p, 1;
  exact ⟨ hp, by norm_num, by norm_num, by rw [ show M / p = 1 by exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith ) ( Nat.div_pos hpM hp.pos ) ] ; exact by have := Erdos287.C_one; norm_num at *; linarith [ hp.two_le ] ⟩

/-
**Excluded prime powers are never denominators.**  If `ExcludedPP M q` and
`q ∣ x`, then `x` cannot belong to a reciprocal-sum-`1` set `A ⊆ [1,M]`.
-/
theorem ExcludedPP.not_dvd_mem {M q : ℕ} (hq : ExcludedPP M q)
    {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) (hAM : ∀ a ∈ A, a ≤ M)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) {x : ℕ} (hxA : x ∈ A) (hqx : q ∣ x) : False := by
  obtain ⟨ p, e, hp, he, rfl, hpC ⟩ := hq;
  apply primePower_window_exclusion A M p e hp hpos hAM hsum he (Nat.le_trans (Nat.le_of_dvd (hpos x hxA) hqx) (hAM x hxA)) hpC x hxA hqx

/-! ## Specialization to a gap-`≤2` counterexample -/

namespace Gap2CE

variable (ce : Gap2CE)

/-
An excluded prime-power multiple is a hole of the counterexample.
-/
theorem notMem_of_excludedPP {q x : ℕ} (hq : ExcludedPP ce.M q) (hqx : q ∣ x) :
    x ∉ ce.A := by
  exact fun hx => ExcludedPP.not_dvd_mem hq ce.hpos (fun a ha => Finset.le_max' _ _ ha) ce.hsum hx hqx

/-
**Reusable blocker pair.**  If `x, x+1 ∈ [N, M]`, `q₁` and `q₂` are excluded
prime powers with `q₁ ∣ x` and `q₂ ∣ x+1`, then no `Gap2CE` exists.
-/
theorem excludedPP_blockerPair {x q₁ q₂ : ℕ}
    (hx0 : ce.N ≤ x) (hx1 : x + 1 ≤ ce.M)
    (hq1 : ExcludedPP ce.M q₁) (hq2 : ExcludedPP ce.M q₂)
    (hd1 : q₁ ∣ x) (hd2 : q₂ ∣ x + 1) : False := by
  exact ce.blockerPair_contradiction hx0 hx1 ( ce.notMem_of_excludedPP hq1 ( by simpa using hd1 ) ) ( ce.notMem_of_excludedPP hq2 ( by simpa using hd2 ) )

/-! ### Propagation rules -/

/-
A hole at `n` inside `[N, M]` forces its right neighbour `n+1` into `A`.
-/
theorem forced_right {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M)
    (hhole : n ∉ ce.A) : n + 1 ∈ ce.A := by
  exact Or.resolve_left ( ce.holes_isolated n hn0 hn1 ) hhole

/-
A hole at `n+1` inside `[N, M]` forces its left neighbour `n` into `A`.
-/
theorem forced_left {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M)
    (hhole : n + 1 ∉ ce.A) : n ∈ ce.A := by
  have := ce.holes_isolated n hn0 hn1; aesop;

end Gap2CE

/-! ## Finite blocker certificates -/

/-- A finite, self-contained certificate refuting a gap-`≤2` counterexample on the
window `[N, M]`: an integer `x` together with two excluded prime powers dividing
`x` and `x+1`. -/
structure BlockerCert where
  /-- Lower window endpoint. -/
  N : ℕ
  /-- Upper window endpoint. -/
  M : ℕ
  /-- The blocking integer; `x` and `x+1` are both holes. -/
  x : ℕ
  /-- The prime power dividing `x`. -/
  q₁ : ℕ
  /-- The prime power dividing `x+1`. -/
  q₂ : ℕ
  /-- `x` lies at or above the lower endpoint. -/
  hNx : N ≤ x
  /-- `x+1` lies at or below the upper endpoint. -/
  hxM : x + 1 ≤ M
  /-- `q₁ ∣ x`. -/
  hdvd₁ : q₁ ∣ x
  /-- `q₂ ∣ x+1`. -/
  hdvd₂ : q₂ ∣ x + 1
  /-- `q₁` is excluded on `[1,M]`. -/
  hexc₁ : ExcludedPP M q₁
  /-- `q₂` is excluded on `[1,M]`. -/
  hexc₂ : ExcludedPP M q₂

/-
**Any valid blocker certificate refutes a `Gap2CE`.**  The certificate is sound
for every counterexample whose window `[ce.N, ce.M]` is contained in the certificate's
window in the sense `ce.M = cert.M` and `ce.N ≤ cert.N`.
-/
theorem BlockerCert.refutes (cert : BlockerCert) (ce : Gap2CE)
    (hM : ce.M = cert.M) (hN : ce.N ≤ cert.N) : False := by
  have := @Gap2CE.excludedPP_blockerPair;
  contrapose! this;
  exact ⟨ ce, cert.x, cert.q₁, cert.q₂, by linarith [ cert.hNx ], by linarith [ cert.hxM ], by exact hM ▸ cert.hexc₁, by exact hM ▸ cert.hexc₂, by exact cert.hdvd₁, by exact cert.hdvd₂, trivial ⟩

/-! ## Generalized good-prime / cofactor blockers

Let `p` be a prime with `M/2 < p ≤ M`.  Then `p` itself is an excluded prime power
(window `1`).  If a neighbour `p ∓ 1` factors as `d · r^e` with `r` a prime whose
base exceeds `C (2d)`, then `r^e` is also excluded (its window is `≤ 2d`), so `p` and
`p ∓ 1` are two adjacent holes — impossible.

The clean, true window bound is `C (2d)` in **both** cases (`p-1` and `p+1`); one does
not need `C (8d)`.  Indeed `M < 2p` gives `M < (2d+1)·r^e`, hence `⌊M/r^e⌋ ≤ 2d`. -/

/-
For `r` prime, `e ≥ 1`, `M < 2p`, and `p ∓ 1 = d·r^e`, the window `⌊M/r^e⌋ ≤ 2d`.
-/
theorem window_le_of_good_prime {M p d r e : ℕ} (hr : r.Prime) (he : 1 ≤ e)
    (hd : 1 ≤ d) (hM2 : M < 2 * p)
    (hcase : p = d * r ^ e + 1 ∨ p + 1 = d * r ^ e) :
    M / r ^ e ≤ 2 * d := by
  rcases hcase with ( rfl | hcase );
  · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.pow_le_pow_right hr.one_lt.le he, Nat.mul_le_mul_left d hr.two_le ] );
  · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.pow_le_pow_right hr.one_lt.le he ] )

namespace Gap2CE

variable (ce : Gap2CE)

/-
**Good-prime blocker (`p-1` case).**  If `p` is a prime with `M/2 < p ≤ M`,
`p - 1 = d · r^e` (written `p = d·r^e + 1`) with `r` prime, `e ≥ 1`, and `C (2d) < r`,
then no `Gap2CE` exists.
-/
theorem goodPrime_blocker_sub {p d r e : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (heq : p = d * r ^ e + 1) (hrC : C (2 * d) < (r : ℤ)) : False := by
  convert BlockerCert.refutes _ _ _ _ using 1;
  exact ⟨ ce.N, ce.M, d * r ^ e, r ^ e, p, by omega, by omega, by simp +decide [ heq ], by simp +decide [ heq ], by
    apply excludedPP_of_le hr he (window_le_of_good_prime hr he hd hM2 (Or.inl heq)) hrC, by
    exact excludedPP_self_of_large hp hpM hM2 ⟩
  all_goals generalize_proofs at *;
  exact ce;
  · rfl;
  · exact le_rfl

/-
**Good-prime blocker (`p+1` case).**  If `p` is a prime with `M/2 < p ≤ M`,
`p + 1 = d · r^e` with `r` prime, `e ≥ 1`, and `C (2d) < r`, then no `Gap2CE` exists.
-/
theorem goodPrime_blocker_add {p d r e : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hd : 1 ≤ d)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (heq : p + 1 = d * r ^ e) (hrC : C (2 * d) < (r : ℤ)) : False := by
  have hexc_r : ExcludedPP ce.M (r ^ e) := by
    apply excludedPP_of_le hr he (window_le_of_good_prime hr he hd hM2 (Or.inr heq)) hrC;
  convert ce.excludedPP_blockerPair ( x := p ) ( q₁ := p ) ( q₂ := r ^ e ) ?_ ?_ ?_ ?_ ?_ ?_ using 1;
  any_goals tauto;
  · exact excludedPP_self_of_large hp ( by linarith ) ( by linarith );
  · exact heq.symm ▸ dvd_mul_left _ _

/-
**Safe-prime blocker.**  If `p = 2r + 1` is a prime with `M/2 < p ≤ M` whose
Sophie-Germain prime `r` satisfies `r > 25 = C 4`, then no `Gap2CE` exists.
(Here `p - 1 = 2·r`, i.e. `d = 2`, `e = 1`.)
-/
theorem safePrime_blocker {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (heq : p = 2 * r + 1) (hr25 : 25 < r) : False := by
  refine ce.goodPrime_blocker_sub ( p := p ) ( d := 2 ) ( r := r ) ( e := 1 ) hp hr le_rfl (by norm_num) hpN hpM hM2 ?_ ?_
  · simpa using heq
  · have h4 : (2 * 2 : ℕ) = 4 := by norm_num
    rw [h4, C_four]
    exact_mod_cast hr25

end Gap2CE

end Erdos287