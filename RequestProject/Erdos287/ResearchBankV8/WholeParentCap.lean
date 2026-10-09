import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2A: the whole-parent SEED-CAP obstruction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The old sufficient hypothesis for seed construction was the package

  denominator-entry  +  every-parent bound `|F_p| ≤ C N_p / (log N_p)^a`, `a > 1`.

This file separates:

1. the **elementary implication** from denominator-entry — every forced coordinate is attributed
   to some parent (`EntryAttribution`), an explicit finite property of the configuration;
2. the **finite forced-neighbour counting identities** — `forced_card_le_sum` (union bound) and
   `forced_card_eq_sum_of_disjoint` (exact identity for disjoint parents), kernel-proved;
3. the **analytic prime-distribution inputs** — a lower bound for the forced set and an upper
   bound for the summed caps, supplied as the explicit structure `CapAnalyticInput`, never
   inhabited here (no Bombieri–Vinogradov / Selberg / Brun–Titchmarsh is proved).

The theorem `old_whole_parent_cap_incompatible` states **only** that the old package is
incompatible with the supplied analytic hypotheses for all sufficiently large `M`.  It does *not*
say that no seed exists: `entry_alone_not_refuted` shows that the analytic inputs are compatible
with denominator-entry by itself.

Status: `OLD_WHOLE_PARENT_CAP = KILLED SUFFICIENT HYPOTHESIS` — **not** `ENTRY = FALSE`.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace WholeParentCap

/-- A family of configurations indexed by the scale `M`. -/
structure CapModel where
  /-- The parents at scale `M`. -/
  parents : ℕ → Finset ℕ
  /-- The parent size `N_p`. -/
  N : ℕ → ℝ
  /-- The forced-neighbour set `F_p` of parent `p` at scale `M`. -/
  F : ℕ → ℕ → Finset ℕ
  /-- The forced set `Z` at scale `M`. -/
  Z : ℕ → Finset ℕ

/-- **Elementary consequence of denominator-entry**: every forced coordinate is attributed to some
parent. -/
def EntryAttribution (m : CapModel) (M : ℕ) : Prop :=
  m.Z M ⊆ (m.parents M).biUnion (m.F M)

/-- The old every-parent SEED-CAP bound with exponent `a` and constant `C`. -/
def ParentCapBound (m : CapModel) (a C : ℝ) (M : ℕ) : Prop :=
  ∀ p ∈ m.parents M, ((m.F M p).card : ℝ) ≤ C * m.N p / Real.log (m.N p) ^ a

/-- **Finite counting (union bound).** -/
theorem forced_card_le_sum (m : CapModel) (M : ℕ) (h : EntryAttribution m M) :
    (m.Z M).card ≤ ∑ p ∈ m.parents M, (m.F M p).card :=
  (Finset.card_le_card h).trans Finset.card_biUnion_le

/-- **Finite counting identity** for pairwise disjoint forced-neighbour sets. -/
theorem forced_card_eq_sum_of_disjoint (m : CapModel) (M : ℕ)
    (hdisj : ∀ p ∈ m.parents M, ∀ q ∈ m.parents M, p ≠ q → Disjoint (m.F M p) (m.F M q)) :
    ((m.parents M).biUnion (m.F M)).card = ∑ p ∈ m.parents M, (m.F M p).card :=
  Finset.card_biUnion hdisj

/-- **External analytic input (never inhabited here).**  A lower bound `Lo M ≤ |Z_M|` for the
forced set, an upper bound for the summed caps, and eventual separation `Up M < Lo M` (this is
where `a > 1` and prime-distribution estimates enter). -/
structure CapAnalyticInput (m : CapModel) (a C : ℝ) where
  /-- Lower bound function. -/
  Lo : ℕ → ℝ
  /-- Upper bound function. -/
  Up : ℕ → ℝ
  /-- Threshold from which the analytic inequalities hold. -/
  M₀ : ℕ
  /-- The forced set is large. -/
  lower : ∀ M ≥ M₀, Lo M ≤ (m.Z M).card
  /-- The summed caps are small. -/
  upper : ∀ M ≥ M₀, ∑ p ∈ m.parents M, C * m.N p / Real.log (m.N p) ^ a ≤ Up M
  /-- Eventual separation. -/
  separation : ∀ M ≥ M₀, Up M < Lo M

/-- **The old whole-parent package is incompatible with the supplied analytic input** for all
sufficiently large `M`.  (It does not say that no seed exists.) -/
theorem old_whole_parent_cap_incompatible (m : CapModel) (a C : ℝ)
    (hin : CapAnalyticInput m a C) :
    ∀ M ≥ hin.M₀, ¬ (EntryAttribution m M ∧ ParentCapBound m a C M) := by
  rintro M hM ⟨hE, hcap⟩
  have h1 : ((m.Z M).card : ℝ) ≤ ∑ p ∈ m.parents M, ((m.F M p).card : ℝ) := by
    exact_mod_cast forced_card_le_sum m M hE
  have h2 : ∑ p ∈ m.parents M, ((m.F M p).card : ℝ) ≤
      ∑ p ∈ m.parents M, C * m.N p / Real.log (m.N p) ^ a :=
    Finset.sum_le_sum hcap
  have := hin.lower M hM
  have := hin.upper M hM
  have := hin.separation M hM
  linarith

/-- A model in which the analytic input holds and denominator-entry holds at every scale. -/
def entryModel : CapModel := ⟨fun _ => {2}, fun _ => 2, fun _ _ => {0}, fun _ => {0}⟩

/-- An analytic input for `entryModel` with cap constant `C = 0`. -/
def entryModelInput (a : ℝ) : CapAnalyticInput entryModel a 0 where
  Lo := fun _ => 1
  Up := fun _ => 0
  M₀ := 0
  lower := fun _ _ => by simp [entryModel]
  upper := fun _ _ => by simp [entryModel]
  separation := fun _ _ => by norm_num

/-- **Firewall: ENTRY alone is not refuted.**  The analytic input is compatible with
denominator-entry at every scale; only the *package* with the whole-parent cap is killed. -/
theorem entry_alone_not_refuted :
    ¬ ∀ (m : CapModel) (a C : ℝ), CapAnalyticInput m a C → ∀ M, ¬ EntryAttribution m M := by
  intro h
  exact h entryModel 2 0 (entryModelInput 2) 0 (by simp [EntryAttribution, entryModel])

/-- In `entryModel` the old cap fails (consistent with the incompatibility theorem). -/
theorem entryModel_cap_fails (a : ℝ) (M : ℕ) : ¬ ParentCapBound entryModel a 0 M := by
  intro h
  have := h 2 (by simp [entryModel])
  simp [entryModel] at this
  linarith

end WholeParentCap
end ResearchBankV8
end Erdos287
