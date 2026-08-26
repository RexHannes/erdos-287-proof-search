import RequestProject.Erdos287.V2SophieBand

/-!
# Erdős Problem #287 — the maximal V2 band, and finite (kernel-checked) window sweeps

Two additions, both finite and both `decide`-checked (never `native_decide`).

## 1. The maximal band

The fixed band `3X/4 < q < 4X/5` of `V2SophieBand.lean` is *not* the largest band the V2
blockers accept.  Their literal requirements are only

  `3 < q`,  `M < 3q`,  `2q + 1 ≤ M`,

because `M < 3q` together with `q ≥ 4` already gives `M < 3q ≤ q²`.  So the maximal
admissible band is `M/3 < q ≤ (M-1)/2`, and `Erdos287.Gap2CE.v2_exact_compiler` is the
corresponding blocker.

## 2. Finite sweeps

`sophieWitness M` is the decidable statement "the maximal band at `M` contains a prime `q`
with `2q - 1` or `2q + 1` prime".  We certify

* `sophieWitness M` for every `39 ≤ M ≤ 250`, hence **no gap-`≤2` counterexample has
  `39 ≤ M ≤ 250`** (`Erdos287.no_Gap2CE_of_M_in_39_250`);
* `¬ sophieWitness 35` — the maximal band really is empty of Sophie primes at `M = 35`, so
  the lower sweep endpoint cannot simply be lowered;
* `¬ ∃ q, prime ∧ V2Band 152 q ∧ (2q±1 prime)` — the *fixed* `3X/4 < q < 4X/5` band has
  genuine supply gaps (here at `M = 152`), which is why the maximal band is used for the
  sweep.

No claim whatsoever is made about the supply of such primes for large `M`.
-/

open scoped BigOperators

namespace Erdos287

namespace Gap2CE

variable (ce : Gap2CE)

/-- **Maximal-band V2 compiler.**  `q > 3` prime with `M < 3q` and `2q + 1 ≤ M`, such that
`2q + 1` or `2q - 1` is prime, refutes every gap-`≤2` counterexample.  The hypothesis
`M < q²` of the underlying blockers is automatic here. -/
theorem v2_exact_compiler {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hM3 : ce.M < 3 * q) (hfit : 2 * q + 1 ≤ ce.M)
    (hp : (2 * q + 1).Prime ∨ (2 * q - 1).Prime) : False := by
  have hsq : ce.M < q * q := by nlinarith
  rcases hp with h | h
  · exact ce.v2_plus_sophie_blocker hq hq3 h rfl (by omega) hM3 hsq
  · exact ce.v2_minus_sophie_blocker hq hq3 h (by omega) (by omega) hM3 hsq

end Gap2CE

/-- The decidable witness predicate: the maximal band at `M` contains a prime `q > 3` with
`2q - 1` or `2q + 1` prime. -/
def sophieWitness (M : ℕ) : Prop :=
  ∃ q ∈ Finset.Icc 2 M, Nat.Prime q ∧ 3 < q ∧ M < 3 * q ∧ 2 * q + 1 ≤ M ∧
    ((2 * q + 1).Prime ∨ (2 * q - 1).Prime)

instance (M : ℕ) : Decidable (sophieWitness M) := by unfold sophieWitness; infer_instance

/-- A witness at `M` refutes every gap-`≤2` counterexample with that `M`. -/
theorem no_Gap2CE_of_sophieWitness (ce : Gap2CE) (h : sophieWitness ce.M) : False := by
  obtain ⟨q, -, hq, hq3, hM3, hfit, hp⟩ := h
  exact ce.v2_exact_compiler hq hq3 hM3 hfit hp

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- Finite sweep: the maximal band supplies a Sophie prime for every `39 ≤ M ≤ 250`. -/
theorem sophieWitness_sweep : ∀ M ∈ Finset.Icc 39 250, sophieWitness M := by decide

/-- **No gap-`≤2` counterexample has `39 ≤ M ≤ 250`.** -/
theorem no_Gap2CE_of_M_in_39_250 (ce : Gap2CE) (h1 : 39 ≤ ce.M) (h2 : ce.M ≤ 250) : False :=
  no_Gap2CE_of_sophieWitness ce (sophieWitness_sweep ce.M (Finset.mem_Icc.2 ⟨h1, h2⟩))

set_option maxRecDepth 10000 in
/-- The sweep cannot start below `39`: at `M = 35` the maximal band contains no prime `q`
with `2q ± 1` prime. -/
theorem not_sophieWitness_35 : ¬ sophieWitness 35 := by decide

set_option maxRecDepth 10000 in
/-- The *fixed* band `3X/4 < q < 4X/5` has genuine supply gaps: at `M = 152` it contains no
prime `q` with `2q ± 1` prime.  (The maximal band does, which is why the sweep above uses
the maximal band.) -/
theorem v2Band_supply_gap_152 :
    ¬ ∃ q ∈ Finset.Icc 2 152, Nat.Prime q ∧ V2Band 152 q ∧
      ((2 * q + 1).Prime ∨ (2 * q - 1).Prime) := by decide

end Erdos287
