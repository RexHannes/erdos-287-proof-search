import RequestProject.Erdos287.ProblemStatement
import RequestProject.Erdos287.V2BandSupplyChecks
import RequestProject.Erdos287.SophieOptimal

/-!
# Erdős Problem #287 — the finite reduction, re-banked as one master theorem

This file re-states the finite (top-layer only) reduction against the **exact** public
predicate `Erdos287Counterexample` of `ProblemStatement.lean`, and repairs the interface
in one respect: the two signs are now kept apart, because they need *different* fitting
endpoints.

* `PlusSophieWitness M q`  : `q` prime, `5 ≤ q`, `M/3 < q`, `2q + 1 ≤ M`, `2q + 1` prime
  (equivalently `M/3 < q ≤ (M-1)/2` with integer floors);
* `MinusSophieWitness M q` : `q` prime, `5 ≤ q`, `M/3 < q`, `2q ≤ M`, `2q - 1` prime
  (equivalently `M/3 < q ≤ ⌊M/2⌋`);
* `SophieWitness M`        : one of the two exists.

`no_Erdos287Counterexample_of_sophieWitness` is the master theorem

  `Erdos287Counterexample A → SophieWitness (max A) → False`.

The condition `5 ≤ q` (equivalently `3 < q` for a prime) is genuinely needed by the
underlying V2 blockers — it is what makes the window `⌊M/q⌋ ≤ 2` fall below `C 2 = 3` —
and it costs nothing on the verified ranges.  The common-endpoint predicate used
previously is *not* called maximal any more; it is simply the coarser interface
`Erdos287.sophieWitness`, and `sophieWitness_imp` records that it implies the repaired one.

A second, free finite blocker is added:

* `maxDivisorPrime_blocker` — if a prime `q > 3` divides `M` and `M < 3q`, no
  counterexample has maximum `M`.  Consequences: **no counterexample has prime maximum**
  (`no_Gap2CE_of_prime_max`) and none has `M = 2q` with `q > 3` prime
  (`no_Gap2CE_of_max_eq_two_mul_prime`).
-/

open scoped BigOperators

namespace Erdos287

/-! ## Sign-sensitive Sophie witnesses -/

/-- Plus witness at `M`: `q` prime, `5 ≤ q`, `M/3 < q ≤ (M-1)/2`, and `2q + 1` prime. -/
def PlusSophieWitness (M q : ℕ) : Prop :=
  q.Prime ∧ 5 ≤ q ∧ M < 3 * q ∧ 2 * q + 1 ≤ M ∧ (2 * q + 1).Prime

/-- Minus witness at `M`: `q` prime, `5 ≤ q`, `M/3 < q ≤ ⌊M/2⌋`, and `2q - 1` prime. -/
def MinusSophieWitness (M q : ℕ) : Prop :=
  q.Prime ∧ 5 ≤ q ∧ M < 3 * q ∧ 2 * q ≤ M ∧ (2 * q - 1).Prime

/-- A Sophie witness at `M` is a plus witness or a minus witness. -/
def SophieWitness (M : ℕ) : Prop :=
  (∃ q, PlusSophieWitness M q) ∨ (∃ q, MinusSophieWitness M q)

/-- The floor form of the plus interval: `M/3 < q` is literally `M < 3q`. -/
theorem plus_interval_floor {M q : ℕ} :
    (M / 3 < q ∧ q ≤ (M - 1) / 2) ↔ (M < 3 * q ∧ 2 * q + 1 ≤ M) := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; omega

/-- The floor form of the minus interval. -/
theorem minus_interval_floor {M q : ℕ} :
    (M / 3 < q ∧ q ≤ M / 2) ↔ (M < 3 * q ∧ 2 * q ≤ M) := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; omega

namespace Gap2CE

variable (ce : Gap2CE)

/-- A plus witness at `M` refutes every gap-`≤2` counterexample with that maximum. -/
theorem no_of_plusSophieWitness {q : ℕ} (h : PlusSophieWitness ce.M q) : False := by
  obtain ⟨hq, hq5, hM3, hfit, hp⟩ := h
  exact ce.v2_plus_sophie_blocker hq (by omega) hp rfl (by omega) hM3 (by nlinarith)

/-- A minus witness at `M` refutes every gap-`≤2` counterexample with that maximum. -/
theorem no_of_minusSophieWitness {q : ℕ} (h : MinusSophieWitness ce.M q) : False := by
  obtain ⟨hq, hq5, hM3, hfit, hp⟩ := h
  exact ce.v2_minus_sophie_blocker hq (by omega) hp (by omega) (by omega) hM3 (by nlinarith)

/-- A Sophie witness at `M` refutes every gap-`≤2` counterexample with that maximum. -/
theorem no_of_sophieWitness (h : SophieWitness ce.M) : False := by
  rcases h with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact ce.no_of_plusSophieWitness hq
  · exact ce.no_of_minusSophieWitness hq

/-! ## The maximum-divisor prime blocker -/

/-- **Maximum-divisor prime blocker.**  If a prime `q > 3` divides the maximum `M` and
`M < 3q`, then no gap-`≤2` counterexample has maximum `M`.

(`q ∣ M` and `M < 3q` force `M = q` or `M = 2q`; the window `⌊M/q⌋ ≤ 2` is below
`C 2 = 3 < q`, so every multiple of `q` — in particular `M` itself — is excluded, while
`M = max A ∈ A`.  The hypothesis `q² > M` that one might expect is *not* needed: it is
implied by `M < 3q` and `q ≥ 4`.) -/
theorem maxDivisorPrime_blocker {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hdvd : q ∣ ce.M) (hM3 : ce.M < 3 * q) : False :=
  ce.notMem_of_excludedPP (excludedPP_of_window_two hq hq3 hM3) hdvd ce.M_mem

/-- No gap-`≤2` counterexample has a prime maximum `> 3`. -/
theorem no_Gap2CE_of_prime_max (hp : ce.M.Prime) (h3 : 3 < ce.M) : False :=
  ce.maxDivisorPrime_blocker hp h3 dvd_rfl (by omega)

/-- No gap-`≤2` counterexample has maximum `2q` with `q > 3` prime. -/
theorem no_Gap2CE_of_max_eq_two_mul_prime {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hM : ce.M = 2 * q) : False :=
  ce.maxDivisorPrime_blocker hq hq3 ⟨2, by omega⟩ (by omega)

end Gap2CE

/-! ## The master theorem against the exact public predicate -/

/-- **Master finite reduction.**  An exact Erdős-#287 counterexample whose maximum admits a
(sign-sensitive) Sophie witness cannot exist. -/
theorem no_Erdos287Counterexample_of_sophieWitness {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hs : SophieWitness (A.max' h.nonempty)) : False :=
  (h.toGap2CE).no_of_sophieWitness hs

/-- No exact counterexample has a prime maximum `> 3`. -/
theorem no_Erdos287Counterexample_of_prime_max {A : Finset ℕ}
    (h : Erdos287Counterexample A) (hp : (A.max' h.nonempty).Prime) : False :=
  (h.toGap2CE).no_Gap2CE_of_prime_max hp (by
    have := h.four_le_max
    exact lt_of_lt_of_le (by norm_num) this)

/-! ## Relation to the coarser common-endpoint interface -/

/-- The previously banked common-endpoint predicate implies the repaired sign-sensitive
one.  (The converse fails for a minus witness with `2q = M`, which the common endpoint
`2q + 1 ≤ M` wrongly excludes.) -/
theorem sophieWitness_imp {M : ℕ} (h : Erdos287.sophieWitness M) : SophieWitness M := by
  obtain ⟨q, -, hq, hq3, hM3, hfit, hp⟩ := h
  have hq4 : q ≠ 4 := by rintro rfl; norm_num at hq
  rcases hp with hp | hp
  · exact Or.inl ⟨q, hq, by omega, hM3, hfit, hp⟩
  · exact Or.inr ⟨q, hq, by omega, hM3, by omega, hp⟩

/-- Bounded (decidable) form of `SophieWitness`. -/
def sophieWitnessB (M : ℕ) : Prop :=
  (∃ q ∈ Finset.Icc (M / 3 + 1) ((M - 1) / 2), PlusSophieWitness M q) ∨
    (∃ q ∈ Finset.Icc (M / 3 + 1) (M / 2), MinusSophieWitness M q)

instance (M : ℕ) : Decidable (sophieWitnessB M) := by
  unfold sophieWitnessB PlusSophieWitness MinusSophieWitness; infer_instance

theorem sophieWitness_of_bounded {M : ℕ} (h : sophieWitnessB M) : SophieWitness M := by
  rcases h with ⟨q, -, hq⟩ | ⟨q, -, hq⟩
  · exact Or.inl ⟨q, hq⟩
  · exact Or.inr ⟨q, hq⟩

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- Finite sweep with the repaired sign-sensitive interface: every `39 ≤ M ≤ 250` has a
Sophie witness. -/
theorem sophieWitnessB_sweep : ∀ M ∈ Finset.Icc 39 250, sophieWitnessB M := by decide

/-- **No exact counterexample has `39 ≤ max A ≤ 250`.** -/
theorem no_Erdos287Counterexample_of_max_in_39_250 {A : Finset ℕ}
    (h : Erdos287Counterexample A) (h1 : 39 ≤ A.max' h.nonempty)
    (h2 : A.max' h.nonempty ≤ 250) : False :=
  no_Erdos287Counterexample_of_sophieWitness h
    (sophieWitness_of_bounded (sophieWitnessB_sweep _ (Finset.mem_Icc.2 ⟨h1, h2⟩)))

end Erdos287
