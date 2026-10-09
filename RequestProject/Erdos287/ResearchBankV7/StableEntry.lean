import RequestProject.Erdos287.ResearchBankV7.PolylogCompletion

/-!
# Erdős #287 — Research Bank V7: STABLE-ENTRY as a feasibility equivalence

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

STABLE-ENTRY is a **reduction / feasibility equivalence**, never an existence theorem.  For a
*fixed legal seed trace* `η₀` it relates

* `HasNo00Extension` : `η₀` has a no-`00` extension `x` with `den(S(x)) ∣ J`;
* `HasNonfailedLeaf`  : `η₀` has a nonfailed terminal leaf in the complete absorption tree.

The two directions have different evidence levels, and this module keeps them apart:

* `stableEntry_forward` (**kernel**, relative to the tracking interface): following an actual
  ENTRY word through the full branching tree produces a terminal node, and the den-condition is
  exactly the non-failure predicate of that node.  Nothing analytic is used.
* `stableEntry_reverse` (**conditional**): realizing a nonfailed terminal leaf by an actual word
  uses the external polylogarithmic simultaneous-completion interface of
  `PolylogCompletion`.
* `stableEntry_equivalence` : the two together, with its conditional premise explicit.

Firewall (`stableEntry_does_not_give_legal_seed`): a feasibility equivalence for a *fixed* seed
never asserts that a legal seed exists.
-/

namespace Erdos287
namespace ResearchBankV7
namespace StableEntry

open Finset

/-! ## 1.  Seeds, words, absorption trees -/

/-- The abstract data of the bounded adaptive-absorption process for a **fixed** legal seed trace
`η₀`: the words extending the seed, the branching tree, and the tracking map that follows a word
through the tree.

Every field is data or a hypothesis about the *encoding*; no field asserts that a legal word or a
legal seed exists. -/
structure AbsorptionSetup where
  /-- The type of candidate extension words of the fixed seed. -/
  Word : Type
  /-- Legality of a word: it extends the fixed seed `η₀` and obeys the no-`00` rule. -/
  Legal : Word → Prop
  /-- The denominator condition `den(S(x)) ∣ J` of a word. -/
  DenDvd : Word → Prop
  /-- The nodes of the complete absorption tree of the fixed seed. -/
  Node : Type
  /-- Terminal (leaf) nodes. -/
  Terminal : Node → Prop
  /-- Failed nodes. -/
  Failed : Node → Prop
  /-- Following a word through the branching tree. -/
  follow : Word → Node
  /-- A legal word is followed to a terminal node of the complete tree. -/
  follow_terminal : ∀ x, Legal x → Terminal (follow x)
  /-- Failure of the reached leaf is *exactly* the failure of the denominator condition: this is
  the definition of a failed leaf in the absorption tree. -/
  failed_iff : ∀ x, Legal x → (Failed (follow x) ↔ ¬ DenDvd x)

namespace AbsorptionSetup

variable (A : AbsorptionSetup)

/-- `η₀` has a no-`00` extension with `den(S) ∣ J`. -/
def HasNo00Extension : Prop := ∃ x : A.Word, A.Legal x ∧ A.DenDvd x

/-- `η₀` has a nonfailed terminal leaf in the complete absorption tree. -/
def HasNonfailedLeaf : Prop := ∃ n : A.Node, A.Terminal n ∧ ¬ A.Failed n

/-- **STABLE-ENTRY, forward direction (kernel, relative to the tracking interface).**  An actual
legal ENTRY word satisfying the denominator condition is followed through the full branching tree
to a terminal leaf which is not failed. -/
theorem stableEntry_forward (h : A.HasNo00Extension) : A.HasNonfailedLeaf := by
  obtain ⟨x, hlegal, hden⟩ := h
  refine ⟨A.follow x, A.follow_terminal x hlegal, ?_⟩
  intro hfail
  exact ((A.failed_iff x hlegal).1 hfail) hden

/-- The realization interface: turning a nonfailed terminal leaf back into an actual word.  This
is where the external polylogarithmic simultaneous-completion input is consumed. -/
def LeafRealization : Prop :=
  ∀ n : A.Node, A.Terminal n → ¬ A.Failed n → ∃ x : A.Word, A.Legal x ∧ A.DenDvd x

/-- **STABLE-ENTRY, reverse direction (conditional).**  Under the leaf-realization interface —
whose only known justification is the external polylog simultaneous-completion input — a nonfailed
terminal leaf yields an actual no-`00` extension with `den(S) ∣ J`. -/
theorem stableEntry_reverse (hreal : A.LeafRealization) (h : A.HasNonfailedLeaf) :
    A.HasNo00Extension := by
  obtain ⟨n, hterm, hfail⟩ := h
  exact hreal n hterm hfail

/-- **STABLE-ENTRY (feasibility equivalence, conditional on the realization interface).** -/
theorem stableEntry_equivalence (hreal : A.LeafRealization) :
    A.HasNo00Extension ↔ A.HasNonfailedLeaf :=
  ⟨A.stableEntry_forward, A.stableEntry_reverse hreal⟩

end AbsorptionSetup

/-- The conditional link to the external interface: a polylog completion law, via an adapter,
supplies the leaf-realization interface.  Both the law and the adapter are external. -/
def RealizationFromPolylog (A : AbsorptionSetup) (dens : ℚ) (k : ℕ) : Prop :=
  PolylogCompletion.PolylogRowCompletionLaw dens k → A.LeafRealization

/-- **CONDITIONAL-BANKED.**  With the external polylog completion law and its adapter, the
STABLE-ENTRY equivalence holds for the fixed seed. -/
theorem stableEntry_equivalence_conditional (A : AbsorptionSetup) {dens : ℚ} {k : ℕ}
    (hadapt : RealizationFromPolylog A dens k)
    (hlaw : PolylogCompletion.PolylogRowCompletionLaw dens k) :
    A.HasNo00Extension ↔ A.HasNonfailedLeaf :=
  A.stableEntry_equivalence (hadapt hlaw)

/-! ## 2.  Firewalls -/

/-- **Firewall.**  `StableEntry` is an equivalence for a *fixed* seed; it does not imply that any
legal seed exists.  Formally, an equivalence never inhabits either of its sides. -/
theorem stableEntry_does_not_give_legal_seed :
    ¬ ∀ P Q : Prop, (P ↔ Q) → P := by
  intro h
  exact (h False False Iff.rfl)

/-- **Firewall.**  A reduction between two feasibility statements is not an existence theorem:
both sides may be uninhabited. -/
theorem feasibility_equivalence_may_be_empty :
    ∃ P Q : Prop, (P ↔ Q) ∧ ¬ P ∧ ¬ Q :=
  ⟨False, False, Iff.rfl, not_false, not_false⟩

/-- A completely empty absorption setup: no candidate words, no nodes.  It satisfies every
hypothesis of the STABLE-ENTRY interface. -/
def emptySetup : AbsorptionSetup :=
  { Word := Empty, Legal := fun _ => False, DenDvd := fun _ => False,
    Node := Empty, Terminal := fun _ => True, Failed := fun _ => True,
    follow := fun x => x.elim,
    follow_terminal := fun x _ => x.elim,
    failed_iff := fun x _ => x.elim }

/-- **Firewall.**  The bounded branching process of STABLE-ENTRY does not settle the current
owner: an absorption setup satisfying the whole interface can have neither a legal word nor a
surviving leaf. -/
theorem bounded_branching_does_not_decide_existence :
    ∃ A : AbsorptionSetup, ¬ A.HasNonfailedLeaf ∧ ¬ A.HasNo00Extension := by
  refine ⟨emptySetup, ?_, ?_⟩
  · rintro ⟨n, -, -⟩
    exact (n : Empty).elim
  · rintro ⟨x, -, -⟩
    exact (x : Empty).elim

end StableEntry
end ResearchBankV7
end Erdos287
