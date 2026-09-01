# Erdős #287 — statement-equivalence audit (2026-09-01)

Purpose: check that what the repository calls "the exact public statement" really is the
published problem, and that no formulation used inside the tree is *weaker* than it.

## 1. The published problem

> Let `1 < n₁ < n₂ < ⋯ < n_k` be integers with `∑_{i} 1/n_i = 1`.
> Must some adjacent gap satisfy `n_{i+1} − n_i ≥ 3`?

Three ingredients: (a) a finite strictly increasing sequence of integers `> 1`;
(b) the reciprocal-sum condition `∑ 1/n_i = 1`; (c) the conclusion "some adjacent gap ≥ 3".

## 2. The formal objects

| Informal ingredient | Formal object | File |
|---|---|---|
| candidate counterexample (set form) | `Erdos287.Erdos287Counterexample (A : Finset ℕ)` | `RequestProject/Erdos287/ProblemStatement.lean` |
| public statement (set form) | `Erdos287.Erdos287Statement := ∀ A, ¬ Erdos287Counterexample A` | `RequestProject/Erdos287/ClosureInputs.lean` |
| public statement (ordered form) | `Erdos287.Erdos287SeqStatement` | `RequestProject/Erdos287/OrderedSequenceBridge.lean` |
| historical compiler type | `Erdos287.Gap2CE` | `RequestProject/Erdos287/Counterexample.lean` |

`Erdos287Counterexample A` has exactly four fields:

* `card_ge : 2 ≤ A.card`;
* `one_lt : ∀ a ∈ A, 1 < a`  (ingredient (a): denominators `> 1`);
* `sum_one : ∑ a ∈ A, (1 : ℚ)/a = 1` (ingredient (b));
* `gap_le_two : ∀ a ∈ A, (∃ b ∈ A, a < b) → (a + 1 ∈ A ∨ a + 2 ∈ A)` (negation of (c)).

A `Finset ℕ` is exactly a finite set of distinct integers, i.e. a strictly increasing finite
sequence up to reindexing; `card_ge` only rules out the degenerate one-term "sequence"
`n₁ = 1`, which is excluded anyway by `one_lt` together with `sum_one`.

## 3. The dictionary, formalised

New in this pass (`RequestProject/Erdos287/OrderedSequenceBridge.lean`):

* `Erdos287.enum` — the increasing enumeration of a `Finset ℕ`, i.e. the passage
  set ⟶ ordered sequence; `enum_mem`, `enum_lt_enum`, `exists_enum_eq`, `enum_succ_le`
  (no element lies strictly between consecutive enumeration values), `sum_enum_recip`.
* `erdos287SeqStatement_of_statement` — set form ⇒ ordered form (existing forward bridge
  `erdos287_seq_of_no_counterexample`, repackaged).
* `erdos287Statement_of_seqStatement` — **ordered form ⇒ set form** (new; this was the
  missing direction).
* `erdos287Statement_iff_seqStatement` — `Erdos287Statement ↔ Erdos287SeqStatement`.
  Hence the set formulation is *not* a weakening of the published one.
* `gap_le_two_iff_orderEmb_gap` — the set-level gap field is literally the adjacent-gap
  condition `n_{i+1} ≤ n_i + 2` on the increasing enumeration.
* `sum_recip_rat_iff_real` — the reciprocal-sum condition may be read in `ℚ` or in `ℝ`.

## 4. `Gap2CE` versus the exact predicate

`Gap2CE` is a strict *relaxation* (it allows the denominator `1` and does not demand two
denominators). The bridge is one-way: `Erdos287Counterexample.toGap2CE`. The countermodel
`A = {1}` (`SemanticFirewalls.singletonGap2CE`, `singleton_not_counterexample`) shows the
converse fails. Consequently:

* refuting `Gap2CE` objects is *stronger* than refuting counterexamples — safe direction;
* no theorem stated for `Gap2CE` may be read as a statement about the public problem
  without the bridge.

## 5. Verdict

STATEMENT-EQUIVALENCE AUDIT: **PASS**. The formal statement is the published statement, the
two public formulations are proved equivalent, and the only auxiliary predicate (`Gap2CE`)
is provably a relaxation used in the safe direction. Nothing in the tree weakens the
problem, and Erdős #287 is **not** claimed to be solved.
