import RequestProject.Erdos287.PostV64V71.ReciprocalFingerprint
import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.ProblemStatement

/-!
# Erdős #287 — V69/V70 source rows: upper-half primes, all good multiples, forced neighbours

**Status: BANK (LEAN PROVED).**  All statements are about a literal hypothetical gap-`≤2`
counterexample (`Gap2CE`, which every exact `Erdos287Counterexample` is, via `toGap2CE`).
Write `N = min A`, `M = max A`.

* `two_mul_N_le_M` — `2N ≤ M` as soon as `M ≥ 4` (from `e(N-1) < M`);
* `upper_half_prime_omitted` — **V69**: a prime `p` with `M < 2p` is never in `A`
  (independent of `Ξ_H`: `p` is the unique `p`-multiple and the reciprocal equation modulo `p`
  rules it out);
* `upper_half_prime_neighbours` — for such `p ≤ M` (and `M ≥ 4`), `p - 1 ∈ A` and `p + 1 ∈ A`
  (the endpoint case `p + 1 = M` is included: then `p + 1 = M ∈ A`);
* `all_good_multiples_omitted` — **V70 Theorem 2.1**: if `q` is prime, `q > M/H`
  (`M < q·H`) and `q ∤ Ξ_H`, then **every** multiple of `q` is omitted;
* `forced_neighbours_selected` — for such `q` and `M/2 < kq < 3M/4`, both `kq - 1 ∈ A` and
  `kq + 1 ∈ A`;
* `adjacent_omissions_false` — two adjacent omissions inside `[N, M]` are impossible.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287

namespace Gap2CE

variable (ce : Erdos287.Gap2CE)

/-- `2N ≤ M` once `M ≥ 4`. -/
theorem two_mul_N_le_M (hM : 4 ≤ ce.M) : 2 * ce.N ≤ ce.M := by
  have hlo := ce.exp_lower
  have he := Real.exp_one_gt_d9
  by_contra hc
  push_neg at hc
  have h1 : (ce.M : ℝ) + 1 ≤ 2 * (ce.N : ℝ) := by exact_mod_cast hc
  have h2 : (4 : ℝ) ≤ ce.M := by exact_mod_cast hM
  nlinarith

/-- Every element lies in `[N, M]`. -/
theorem le_M {a : ℕ} (ha : a ∈ ce.A) : a ≤ ce.M := Finset.le_max' _ _ ha

/-- **V69 upper-half prime omission**: a prime `p` with `M < 2p` is never a denominator. -/
theorem upper_half_prime_omitted {p : ℕ} (hp : p.Prime) (hp2 : ce.M < 2 * p) : p ∉ ce.A := by
  intro hpA
  have hpM : p ≤ ce.M := (le_M ce) hpA
  exact ce.notMem_of_excludedPP (excludedPP_self_of_large hp hpM hp2) dvd_rfl hpA

/-- **Two adjacent omissions inside `[N, M]` are impossible.** -/
theorem adjacent_omissions_false {n : ℕ} (hn0 : ce.N ≤ n) (hn1 : n + 1 ≤ ce.M)
    (h1 : n ∉ ce.A) (h2 : n + 1 ∉ ce.A) : False :=
  ce.blockerPair_contradiction hn0 hn1 h1 h2

/-- An omitted `n` with `N < n < M` has both neighbours selected. -/
theorem neighbours_of_hole {n : ℕ} (hn0 : ce.N < n) (hn1 : n < ce.M) (hn : n ∉ ce.A) :
    n - 1 ∈ ce.A ∧ n + 1 ∈ ce.A := by
  constructor
  · have := ce.holes_isolated (n - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at this
    exact this.resolve_right hn
  · exact (ce.holes_isolated n (by omega) (by omega)).resolve_left hn

/-- **V69 forced neighbours of an upper-half prime** (`M ≥ 4`, `M/2 < p ≤ M`):
`p - 1 ∈ A` and `p + 1 ∈ A`.  (If `p + 1 = M`, this is just `M ∈ A`.) -/
theorem upper_half_prime_neighbours (hM : 4 ≤ ce.M) {p : ℕ} (hp : p.Prime)
    (hp2 : ce.M < 2 * p) (hpM : p ≤ ce.M) : p - 1 ∈ ce.A ∧ p + 1 ∈ ce.A := by
  have hnot := (upper_half_prime_omitted ce) hp hp2
  have hN := (two_mul_N_le_M ce) hM
  have hpM' : p < ce.M := lt_of_le_of_ne hpM (fun h => hnot (h ▸ ce.M_mem))
  exact (neighbours_of_hole ce) (by omega) hpM' hnot

/-- **V70 Theorem 2.1 (all good multiples omitted).**  If `q` is prime, `q > M/H`
(i.e. `M < q·H`) and `q ∤ Ξ_H`, then no multiple of `q` belongs to `A`. -/
theorem all_good_multiples_omitted {H q : ℕ} (hq : q.Prime) (hqH : ce.M < q * H)
    (hXi : ¬ q ∣ Xi H) {n : ℕ} (hqn : q ∣ n) : n ∉ ce.A := fun hn =>
  good_large_prime_row_empty ce.A ce.M H q hq ce.hpos (fun _ ha => (le_M ce) ha) ce.hsum
    (div_le_of_lt_mul hqH) hXi n hn hqn

/-- **V70 forced neighbours.**  For a good prime `q` (`q` prime, `M < q·H`, `q ∤ Ξ_H`) and
`M/2 < kq < 3M/4`, both `kq - 1` and `kq + 1` are selected. -/
theorem forced_neighbours_selected (hM : 4 ≤ ce.M) {H q k : ℕ} (hq : q.Prime)
    (hqH : ce.M < q * H) (hXi : ¬ q ∣ Xi H) (hlo : ce.M < 2 * (k * q))
    (hhi : 4 * (k * q) < 3 * ce.M) : k * q - 1 ∈ ce.A ∧ k * q + 1 ∈ ce.A := by
  have hnot := (all_good_multiples_omitted ce) hq hqH hXi (dvd_mul_left q k)
  have hN := (two_mul_N_le_M ce) hM
  exact (neighbours_of_hole ce) (by omega) (by omega) hnot

end Gap2CE

/-! ## The same statements for exact `Erdos287Counterexample`s -/

namespace Erdos287Counterexample

variable {A : Finset ℕ} (h : Erdos287Counterexample A)

/-- V69 for exact counterexamples. -/
theorem upper_half_prime_omitted {p : ℕ} (hp : p.Prime) (hp2 : A.max' h.nonempty < 2 * p) :
    p ∉ A :=
  Gap2CE.upper_half_prime_omitted h.toGap2CE hp hp2

/-- V70 Theorem 2.1 for exact counterexamples. -/
theorem all_good_multiples_omitted {H q : ℕ} (hq : q.Prime) (hqH : A.max' h.nonempty < q * H)
    (hXi : ¬ q ∣ Xi H) {n : ℕ} (hqn : q ∣ n) : n ∉ A :=
  Gap2CE.all_good_multiples_omitted h.toGap2CE hq hqH hXi hqn

/-- V70 forced neighbours for exact counterexamples. -/
theorem forced_neighbours_selected (hM : 4 ≤ A.max' h.nonempty) {H q k : ℕ} (hq : q.Prime)
    (hqH : A.max' h.nonempty < q * H) (hXi : ¬ q ∣ Xi H)
    (hlo : A.max' h.nonempty < 2 * (k * q)) (hhi : 4 * (k * q) < 3 * A.max' h.nonempty) :
    k * q - 1 ∈ A ∧ k * q + 1 ∈ A :=
  Gap2CE.forced_neighbours_selected h.toGap2CE hM hq hqH hXi hlo hhi

end Erdos287Counterexample

end Erdos287.PostV64V71
