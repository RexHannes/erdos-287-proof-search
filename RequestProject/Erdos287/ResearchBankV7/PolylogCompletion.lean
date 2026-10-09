import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V7: fixed-polylog completion, with explicit dependency status

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The interface banked here is

> positive-density available row  +  cofactor length at least a fixed polylogarithmic threshold
> ⟹ a complete-row law with polylogarithmic support and controlled coordinate marginals.

Its dependencies are separated and **each is recorded at its true evidence level**:

| ingredient | status in this project |
| --- | --- |
| Croot reciprocal subset-sum input (`CrootReciprocalSubsetSum`) | external, uninhabited |
| PNT / prime-factor supply (`PrimeFactorSupply`) | external, uninhabited |
| finite second-moment argument (`finite_second_moment`) | **kernel-proved here** |
| disjoint buffer packing (`buffer_packing`) | **kernel-proved here** |
| LLL / whole-row simultaneous completion (`SimultaneousRowCompletionInput`) | external, uninhabited |

Consequently `polylog_completion_conditional` is **CONDITIONAL-BANKED**, never `kernelProof`:
it is an implication whose premises include propositions that are not proved in Lean anywhere in
this project.  The firewall `conditional_does_not_inhabit_conclusion` is machine-checked.
-/

namespace Erdos287
namespace ResearchBankV7
namespace PolylogCompletion

open Finset

/-! ## 1.  The elementary finite components (kernel-proved) -/

/-- **Finite second-moment (Chebyshev) inequality, kernel.**  In a finite family, the number of
coordinates deviating from `μ` by at least `t` is controlled by the second moment. -/
theorem finite_second_moment (s : Finset ℕ) (f : ℕ → ℚ) (μ t : ℚ) (ht : 0 < t) :
    t ^ 2 * ({x ∈ s | t ≤ |f x - μ|}.card : ℚ) ≤ ∑ x ∈ s, (f x - μ) ^ 2 := by
  classical
  set D : Finset ℕ := {x ∈ s | t ≤ |f x - μ|} with hD
  have hDs : D ⊆ s := Finset.filter_subset _ _
  have h1 : t ^ 2 * (D.card : ℚ) ≤ ∑ x ∈ D, (f x - μ) ^ 2 := by
    rw [mul_comm, ← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum D _ _ ?_
    intro x hx
    have hx' : t ≤ |f x - μ| := (Finset.mem_filter.1 hx).2
    have : t ^ 2 ≤ |f x - μ| ^ 2 := by
      have h0 : (0:ℚ) ≤ t := le_of_lt ht
      nlinarith [hx', h0]
    simpa [sq_abs] using this
  have h2 : ∑ x ∈ D, (f x - μ) ^ 2 ≤ ∑ x ∈ s, (f x - μ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hDs (fun x _ _ => sq_nonneg _)
  linarith

/-- **Disjoint buffer packing, kernel.**  Pairwise disjoint buffers inside a common ground set use
at most `|T|` coordinates in total. -/
theorem buffer_packing {T : Finset ℕ} {ι : Finset ℕ} (buf : ℕ → Finset ℕ)
    (hsub : ∀ i ∈ ι, buf i ⊆ T)
    (hdisj : ∀ i ∈ ι, ∀ j ∈ ι, i ≠ j → Disjoint (buf i) (buf j)) :
    ∑ i ∈ ι, (buf i).card ≤ T.card := by
  classical
  have hcard : (ι.biUnion buf).card = ∑ i ∈ ι, (buf i).card :=
    Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)
  have hsub' : ι.biUnion buf ⊆ T := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    exact hsub i hi hxi
  calc ∑ i ∈ ι, (buf i).card = (ι.biUnion buf).card := hcard.symm
    _ ≤ T.card := Finset.card_le_card hsub'

/-! ## 2.  The external analytic inputs (uninhabited here) -/

/-- **EXTERNAL (uninhabited here).**  Croot's reciprocal subset-sum theorem: there is an absolute
constant `C` such that any set of integers in `[n, C n]` whose reciprocal sum is at least `2`
contains a subset of reciprocals summing exactly to `1`.  Not formalized in this project. -/
def CrootReciprocalSubsetSum : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ A : Finset ℕ, A ⊆ Finset.Icc n (C * n) →
    2 ≤ ∑ a ∈ A, (1 : ℚ) / a → ∃ S ⊆ A, ∑ a ∈ S, (1 : ℚ) / a = 1

/-- The prime counting function `π(M)`, as a finite count. -/
def piCount (M : ℕ) : ℕ := ((Finset.Icc 1 M).filter Nat.Prime).card

/-- **EXTERNAL (uninhabited here).**  The prime-counting / prime-factor supply input in
Prime-Number-Theorem strength.  Not formalized in this project. -/
def PrimeFactorSupply : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    (1 - ε) * (M / Real.log M) ≤ (piCount M : ℝ)

/-- **EXTERNAL (uninhabited here).**  The Lovász-Local-Lemma style whole-row simultaneous
completion input: individually completable rows with sparse dependency can be completed
*simultaneously* and disjointly.  Stated as a parameterized interface over the row family, the
available coordinates and the per-row targets; not formalized in this project. -/
def SimultaneousRowCompletionInput (rows : Finset ℕ) (avail : ℕ → Finset ℕ) (target : ℕ → ℚ)
    (bound : ℕ) : Prop :=
  (∀ r ∈ rows, ∃ S ⊆ avail r, ∑ n ∈ S, (1 : ℚ) / n = target r ∧ S.card ≤ bound) →
  ∃ sel : ℕ → Finset ℕ,
    (∀ r ∈ rows, sel r ⊆ avail r) ∧
    (∀ r ∈ rows, ∀ r' ∈ rows, r ≠ r' → Disjoint (sel r) (sel r')) ∧
    (∀ r ∈ rows, ∑ n ∈ sel r, (1 : ℚ) / n = target r) ∧
    (∀ r ∈ rows, (sel r).card ≤ bound)

/-! ## 3.  The fixed-polylog complete-row law -/

/-- The complete-row law with polylogarithmic support and controlled coordinate marginals
(deterministic surrogate: the produced support avoids any prescribed forbidden set of at most half
the available coordinates).

This is a **research interface**, not a theorem of this layer. -/
def PolylogRowCompletionLaw (dens : ℚ) (k : ℕ) : Prop :=
  ∃ Cpoly : ℕ, ∀ (M : ℕ) (avail forbidden : Finset ℕ) (target : ℚ),
    avail ⊆ Finset.Icc 1 M →
    dens * M ≤ avail.card →                                   -- positive-density available row
    (Nat.log 2 M) ^ k ≤ avail.card →                          -- fixed polylog cofactor length
    2 * forbidden.card ≤ avail.card →                         -- controlled coordinate marginals
    (∃ S ⊆ avail, ∑ n ∈ S, (1 : ℚ) / n = target) →            -- the target is feasible at all
    ∃ S ⊆ avail, ∑ n ∈ S, (1 : ℚ) / n = target ∧
      S.card ≤ Cpoly * (Nat.log 2 M) ^ k ∧ Disjoint S forbidden

/-- The complete dependency package of the polylog completion interface. -/
def PolylogCompletionDependencies (rows : Finset ℕ) (avail : ℕ → Finset ℕ) (target : ℕ → ℚ)
    (bound : ℕ) : Prop :=
  CrootReciprocalSubsetSum ∧ PrimeFactorSupply ∧
    SimultaneousRowCompletionInput rows avail target bound

/-- The adapter that would turn the dependency package into the complete-row law.  It is itself an
**external** object: no Lean proof of it exists in this project. -/
def PolylogCompletionAdapter (dens : ℚ) (k : ℕ) (rows : Finset ℕ) (avail : ℕ → Finset ℕ)
    (target : ℕ → ℚ) (bound : ℕ) : Prop :=
  PolylogCompletionDependencies rows avail target bound → PolylogRowCompletionLaw dens k

/-- **CONDITIONAL-BANKED.**  The fixed-polylog complete-row law follows from its four external
inputs through the adapter — and only that way.  The finite ingredients
(`finite_second_moment`, `buffer_packing`) are the parts proved in this project. -/
theorem polylog_completion_conditional {dens : ℚ} {k : ℕ} {rows : Finset ℕ} {avail : ℕ → Finset ℕ}
    {target : ℕ → ℚ} {bound : ℕ}
    (hadapter : PolylogCompletionAdapter dens k rows avail target bound)
    (hdeps : PolylogCompletionDependencies rows avail target bound) :
    PolylogRowCompletionLaw dens k :=
  hadapter hdeps

/-! ## 4.  Firewalls -/

/-- **Firewall.**  A conditional theorem never inhabits its conclusion: as long as the external
inputs are uninhabited, `PolylogRowCompletionLaw` is not available as a proved statement. -/
theorem conditional_does_not_inhabit_conclusion :
    ¬ ∀ P Q : Prop, (P → Q) → Q := by
  intro h
  exact h False False id

/-- **Firewall.**  The two finite ingredients proved here do **not** add up to the analytic
statement: a conjunction of proved lemmas together with an unproved input is exactly as strong as
the unproved input. -/
theorem finite_ingredients_do_not_replace_analytic_input :
    ¬ ∀ P Q : Prop, P → (P ∧ Q) := by
  intro h
  exact (h True False trivial).2

end PolylogCompletion
end ResearchBankV7
end Erdos287
