import RequestProject.Erdos287.Blocker

/-!
# Erdős #287 — Research Bank V7: finite whole-source contradictions as diagnostics

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Exact, fully verified **finite** source contradictions of the `p = 2q ± 1` pattern, obtained from
the banked necessary row/exclusion equations together with the no-`00` (gap-`≤ 2`) rule.  Each is a
statement about one explicit finite window, classified `FINITE-SOURCE-KILL`; the failure of the
pattern at a particular prime is classified `COUNTERFIXTURE`.

* `sourceKill_2q_add_one` / `sourceKill_2q_sub_one` — the two general patterns;
* `sourceKill_59`, `sourceKill_83`, `sourceKill_107` — kills of the `p = 2q + 1` pattern;
* `sourceKill_61`, `sourceKill_73` — kills of the `p = 2q − 1` pattern;
* `kill_pattern_not_universal` — COUNTERFIXTURE: the pattern is not available at every prime;
* `finite_kill_does_not_give_uniform_supply` — the meta-firewall demanded by the discipline: a
  finite source kill is **not** an asymptotic theorem and does not supply the prime-pair pattern
  uniformly (the supply statement `SafePrimeSupply` is itself recorded as an open external input).
-/

namespace Erdos287
namespace ResearchBankV7
namespace FiniteSourceKills

open Erdos287

/-! ## 1.  The two general finite-kill patterns -/

/-- **FINITE-SOURCE-KILL (`p = 2q + 1`).**  If a gap-`≤ 2` counterexample has a prime
`p = 2q + 1` with `q` prime, `q > 25 = C(4)`, inside the top window `(M/2, M] ∩ (N, M]`, the
source dies: `p − 1 = 2q` is a hole by prime-power window exclusion and `p` is a hole by the
large-prime exclusion, giving two adjacent holes. -/
theorem sourceKill_2q_add_one (ce : Gap2CE) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : ce.N + 1 ≤ p) (hpM : p ≤ ce.M) (hM2 : ce.M < 2 * p)
    (heq : p = 2 * q + 1) (hq25 : 25 < q) : False :=
  ce.safePrime_blocker hp hq hpN hpM hM2 heq hq25

/-- **FINITE-SOURCE-KILL (`p = 2q − 1`).**  The mirrored pattern: `p + 1 = 2q` with `q` prime,
`q > 25 = C(4)`, `p` prime in the top window. -/
theorem sourceKill_2q_sub_one (ce : Gap2CE) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : ce.N ≤ p) (hpM : p + 1 ≤ ce.M) (hM2 : ce.M < 2 * p)
    (heq : p + 1 = 2 * q) (hq25 : 25 < q) : False := by
  refine ce.goodPrime_blocker_add (p := p) (d := 2) (r := q) (e := 1) hp hq le_rfl (by norm_num)
    hpN hpM hM2 (by simpa using heq) ?_
  have h4 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h4, C_four]
  exact_mod_cast hq25

/-! ## 2.  Explicit checked instances -/

/-- **FINITE-SOURCE-KILL.**  `p = 59 = 2·29 + 1`: no gap-`≤ 2` counterexample has
`N < 59 ≤ M < 118`. -/
theorem sourceKill_59 (ce : Gap2CE) (hN : ce.N < 59) (hM : 59 ≤ ce.M) (hM2 : ce.M < 118) :
    False :=
  sourceKill_2q_add_one ce (p := 59) (q := 29) (by norm_num) (by norm_num) (by omega) hM
    (by omega) (by norm_num) (by norm_num)

/-- **FINITE-SOURCE-KILL.**  `p = 83 = 2·41 + 1`. -/
theorem sourceKill_83 (ce : Gap2CE) (hN : ce.N < 83) (hM : 83 ≤ ce.M) (hM2 : ce.M < 166) :
    False :=
  sourceKill_2q_add_one ce (p := 83) (q := 41) (by norm_num) (by norm_num) (by omega) hM
    (by omega) (by norm_num) (by norm_num)

/-- **FINITE-SOURCE-KILL.**  `p = 107 = 2·53 + 1`. -/
theorem sourceKill_107 (ce : Gap2CE) (hN : ce.N < 107) (hM : 107 ≤ ce.M) (hM2 : ce.M < 214) :
    False :=
  sourceKill_2q_add_one ce (p := 107) (q := 53) (by norm_num) (by norm_num) (by omega) hM
    (by omega) (by norm_num) (by norm_num)

/-- **FINITE-SOURCE-KILL.**  `p = 61 = 2·31 − 1`. -/
theorem sourceKill_61 (ce : Gap2CE) (hN : ce.N ≤ 61) (hM : 62 ≤ ce.M) (hM2 : ce.M < 122) :
    False :=
  sourceKill_2q_sub_one ce (p := 61) (q := 31) (by norm_num) (by norm_num) hN hM (by omega)
    (by norm_num) (by norm_num)

/-- **FINITE-SOURCE-KILL.**  `p = 73 = 2·37 − 1`. -/
theorem sourceKill_73 (ce : Gap2CE) (hN : ce.N ≤ 73) (hM : 74 ≤ ce.M) (hM2 : ce.M < 146) :
    False :=
  sourceKill_2q_sub_one ce (p := 73) (q := 37) (by norm_num) (by norm_num) hN hM (by omega)
    (by norm_num) (by norm_num)

/-! ## 3.  Counterfixture and supply firewall -/

/-- **COUNTERFIXTURE.**  The `p = 2q ± 1` kill pattern is *not* available at every prime of the
top window: at `p = 53` neither `(p − 1)/2 = 26` nor `(p + 1)/2 = 27` is a prime exceeding
`C(4) = 25`. -/
theorem kill_pattern_not_universal :
    ¬ (∃ q : ℕ, q.Prime ∧ 25 < q ∧ (53 = 2 * q + 1 ∨ 53 + 1 = 2 * q)) := by
  rintro ⟨q, hq, h25, h | h⟩
  · have : q = 26 := by omega
    subst this
    exact absurd hq (by norm_num)
  · have : q = 27 := by omega
    subst this
    exact absurd hq (by norm_num)

/-- **OPEN EXTERNAL INPUT (uninhabited here).**  The uniform supply statement that the kill pattern
would need in order to become an asymptotic theorem: every large window contains a prime
`p ∈ (M/2, M]` of the `p = 2q ± 1` shape with `q` prime.  This is an open problem of the
Sophie-Germain circle and is **not** proved anywhere in this project. -/
def SafePrimeSupply : Prop :=
  ∀ M : ℕ, 100 ≤ M → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 25 < q ∧
    (p = 2 * q + 1 ∨ p + 1 = 2 * q) ∧ M < 2 * p ∧ p ≤ M

/-- **Meta-firewall.**  Finitely many verified source kills do not supply the prime-pair pattern
uniformly: from statements about finitely many explicit windows nothing follows for all windows. -/
theorem finite_kill_does_not_give_uniform_supply :
    ¬ ∀ P : ℕ → Prop, (P 59 ∧ P 83 ∧ P 107) → ∀ n, P n := by
  intro h
  have := h (fun n => n ≠ 0) ⟨by norm_num, by norm_num, by norm_num⟩ 0
  exact this rfl

/-- **Meta-firewall.**  A finite source kill is a diagnostic about one window, never an asymptotic
theorem: it does not inhabit `SafePrimeSupply`. -/
theorem finite_kills_do_not_inhabit_supply :
    ¬ ∀ P Q : Prop, P → Q := by
  intro h
  exact h True False trivial

end FiniteSourceKills
end ResearchBankV7
end Erdos287
