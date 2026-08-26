import Mathlib
import RequestProject.Erdos287.Blocker
import RequestProject.Erdos287.PrimeFree
import RequestProject.TrustedBank.Erdos287.CarryTower

/-!
# Trusted bank — Erdős #287: top-layer consequences and the generalized
fixed-cofactor blocker

The already-certified machinery is *reused*, not rewritten.  In particular this file
does not restate:

* `Erdos287.topLayer_congruence` (the top-layer congruence),
* `Erdos287.topLayer_card_ne_one` (the maximal `p`-adic fibre is never a singleton),
* `Erdos287.primePower_window_exclusion`, `Erdos287.ExcludedPP`,
* `Erdos287.Gap2CE.blockerPair_contradiction`, `Erdos287.Gap2CE.excludedPP_blockerPair`,
* `Erdos287.Gap2CE.goodPrime_blocker_sub` / `_add`,
* the carry-tower statements of `TrustedBank.CarryTower`.

What is added here is the missing **generalized fixed-cofactor blocker** with every
numerical hypothesis spelled out, derived from that bank alone.

### Audit remark on the threshold

The prompt's threshold `q > C(2j-1)` is **not sufficient as stated**: from
`p = j·q ± 1` and `M < 2p` one only gets `⌊M/q⌋ ≤ 2j`, and `⌊M/q⌋ = 2j` really does
occur (e.g. `M = 2p - 2 = 2jq` in the `p = jq+1` case).  Since `C` is only monotone,
`C(2j-1) < r` does not imply `C(2j) < r`.  We therefore bank two forms:

* `fixedCofactor_blocker_sub` / `_add`, with the *correct* threshold `C(2j) < r`;
* `fixedCofactor_blocker_sub_sharpWindow`, with the prompt's threshold `C(2j-1) < r`
  **plus** the explicit window hypothesis `⌊M/q⌋ ≤ 2j-1` that makes it legitimate.
-/

open scoped BigOperators

namespace TrustedBank
namespace Erdos287Blockers

open Erdos287

namespace Gap2CE

variable (ce : Gap2CE)

/-- If `p` is a prime in the top interval `(M/2, M]` above `N`, and some excluded
prime power divides `p - 1`, then no gap-`≤2` counterexample exists. -/
theorem blocker_of_excluded_neighbour_sub {p q : ℕ} (hp : p.Prime)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hq : ExcludedPP ce.M q) (hdvd : q ∣ p - 1) : False := by
  have hp2 := hp.two_le
  have hsucc : p - 1 + 1 = p := by omega
  refine ce.excludedPP_blockerPair (x := p - 1) (q₁ := q) (q₂ := p) (by omega) (by omega)
    hq (excludedPP_self_of_large hp hpM hM2) hdvd ?_
  rw [hsucc]

/-- If `p` is a prime in the top interval `(M/2, M]` with `p + 1 ≤ M`, and some excluded
prime power divides `p + 1`, then no gap-`≤2` counterexample exists. -/
theorem blocker_of_excluded_neighbour_add {p q : ℕ} (hp : p.Prime)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hq : ExcludedPP ce.M q) (hdvd : q ∣ p + 1) : False :=
  ce.excludedPP_blockerPair (x := p) (q₁ := p) (q₂ := q) hpN hpM
    (excludedPP_self_of_large hp (by omega) hM2) hq dvd_rfl hdvd

/-- **Generalized fixed-cofactor blocker (`p = j·q - 1`… written `p = j·q + 1`).**

All numerical hypotheses are explicit:
`q = r^e` a prime power (`r` prime, `e ≥ 1`), `j ≥ 1` the fixed cofactor,
`p = j·q + 1` prime, `p` in the top interval (`N < p ≤ M` and `M < 2p`),
`q² > M`, and `r` above the certified subset-numerator threshold `C(2j)`.
Then a gap-`≤2` counterexample is impossible.

The hypothesis `q² > M` is retained because the specification lists it; the proof does
not use it. -/
theorem fixedCofactor_blocker_sub {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hj : 1 ≤ j) (hq : q = r ^ e)
    (heq : p = j * q + 1)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hqsq : ce.M < q ^ 2) (hthr : C (2 * j) < (r : ℤ)) : False := by
  subst hq
  exact ce.goodPrime_blocker_sub hp hr he hj hpN hpM hM2 heq hthr

/-- **Generalized fixed-cofactor blocker (`p = j·q - 1`, i.e. `p + 1 = j·q`).**
Same explicit hypotheses; again `q² > M` is retained but unused. -/
theorem fixedCofactor_blocker_add {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hj : 1 ≤ j) (hq : q = r ^ e)
    (heq : p + 1 = j * q)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hqsq : ce.M < q ^ 2) (hthr : C (2 * j) < (r : ℤ)) : False := by
  subst hq
  exact ce.goodPrime_blocker_add hp hr he hj hpN hpM hM2 heq hthr

/-- **The sharp-window form with the threshold `C(2j-1)`.**  This is the prompt's
statement, made correct by adding the window hypothesis `⌊M/q⌋ ≤ 2j-1` (without it the
window can be `2j`, and `C(2j-1) < r` is then not enough).  The hypothesis `1 ≤ j` is not
needed here (it is implied by `p` prime and `p = j·q + 1`), so it is omitted. -/
theorem fixedCofactor_blocker_sub_sharpWindow {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hq : q = r ^ e)
    (heq : p = j * q + 1)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hwin : ce.M / q ≤ 2 * j - 1) (hthr : C (2 * j - 1) < (r : ℤ)) : False := by
  have hexc : ExcludedPP ce.M q := by
    subst hq
    exact excludedPP_of_le hr he hwin hthr
  refine blocker_of_excluded_neighbour_sub ce hp hpN hpM hM2 hexc ?_
  have : p - 1 = j * q := by omega
  rw [this]
  exact Dvd.intro j (mul_comm q j)

/-- The same sharp-window form on the `p + 1` side. -/
theorem fixedCofactor_blocker_add_sharpWindow {p q r e j : ℕ}
    (hp : p.Prime) (hr : r.Prime) (he : 1 ≤ e) (hq : q = r ^ e)
    (heq : p + 1 = j * q)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (hwin : ce.M / q ≤ 2 * j - 1) (hthr : C (2 * j - 1) < (r : ℤ)) : False := by
  have hexc : ExcludedPP ce.M q := by
    subst hq
    exact excludedPP_of_le hr he hwin hthr
  refine blocker_of_excluded_neighbour_add ce hp hpN hpM hM2 hexc ?_
  rw [heq]
  exact Dvd.intro j (mul_comm q j)

end Gap2CE

end Erdos287Blockers
end TrustedBank
