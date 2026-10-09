import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V6: the middle-band same-trace theorem (CONDITIONAL)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The canonical middle-band statement is the *same-trace* statement: a feasible frozen-core/top trace
can be preserved while completing all relevant middle rows.

It is **not** manufactured here from weaker interfaces.  Completing a middle row at a *fixed
cardinality* and a *prescribed residue* requires a fixed-cardinality additive theorem of
Dias da Silva–Hamidoune type.  That theorem is neither in this project nor used from Mathlib here,
so it is recorded as the **uninhabited** interface `RestrictedSumsetInput`, and every statement of
this file that depends on it is an implication consuming it as a hypothesis.

Classification: `conditionalInterface`.  **Not** `kernelProof`.

Kernel-proved without any interface:

* `completion_preserves_trace`, `completion_agrees_on_middle` — the trace-preservation bookkeeping
  of a completion supported on coordinates disjoint from the frozen core/top trace.
-/

namespace Erdos287
namespace ResearchBankV6
namespace MiddleBand

open Finset

/-! ## 1.  The required fixed-cardinality additive interface (uninhabited) -/

/-- **(DDS-H-INTERFACE), required external additive input.**  For a prime `p`, a set `A` of
residues and a cardinality `h ≤ |A|`, the set of sums of `h`-element subsets of `A` has at least
`min (p, h(|A| − h) + 1)` elements.

This is the exact fixed-cardinality (restricted sumset) input the middle band needs.  It is
**uninhabited here**: no proof is supplied, in this project or from Mathlib. -/
def RestrictedSumsetInput : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (A : Finset (ZMod p)) (h : ℕ), h ≤ A.card →
    min p (h * (A.card - h) + 1) ≤ ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)).card

/-! ## 2.  Consequences of the interface (all conditional) -/

/-- **CONDITIONAL.**  If the fixed-cardinality additive interface holds and the row is long enough
(`p ≤ h(|A| − h) + 1`), then every prescribed residue `r` is realized by an `h`-element subset of
the available cofactor residues. -/
theorem restrictedSumset_covers (hin : RestrictedSumsetInput) {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) (h : ℕ) (hh : h ≤ A.card) (hlong : p ≤ h * (A.card - h) + 1)
    (r : ZMod p) : ∃ B ⊆ A, B.card = h ∧ ∑ x ∈ B, x = r := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard := hin p hp A h hh
  rw [min_eq_left hlong] at hcard
  have huniv : ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    have hle : ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)).card ≤ Fintype.card (ZMod p) :=
      Finset.card_le_univ _
    rw [ZMod.card p] at hle ⊢
    omega
  have hr : r ∈ ((A.powersetCard h).image (fun B => ∑ x ∈ B, x)) := by rw [huniv]; exact mem_univ r
  obtain ⟨B, hB, hsum⟩ := Finset.mem_image.1 hr
  obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.1 hB
  exact ⟨B, hBsub, hBcard, hsum⟩

/-- **CONDITIONAL (middle rows completable).**  Under the fixed-cardinality additive interface,
all relevant middle rows can be completed simultaneously at their prescribed cardinalities and
prescribed residues. -/
theorem middleRows_completable {ι : Type*} (hin : RestrictedSumsetInput) (rows : Finset ι)
    (p : ι → ℕ) (hp : ∀ i ∈ rows, (p i).Prime)
    (A : (i : ι) → Finset (ZMod (p i))) (h : ι → ℕ)
    (hh : ∀ i ∈ rows, h i ≤ (A i).card)
    (hlong : ∀ i ∈ rows, p i ≤ h i * ((A i).card - h i) + 1)
    (r : (i : ι) → ZMod (p i)) :
    ∃ B : (i : ι) → Finset (ZMod (p i)),
      ∀ i ∈ rows, B i ⊆ A i ∧ (B i).card = h i ∧ ∑ x ∈ B i, x = r i := by
  have key : ∀ i : ι, ∃ Bi : Finset (ZMod (p i)),
      i ∈ rows → (Bi ⊆ A i ∧ Bi.card = h i ∧ ∑ x ∈ Bi, x = r i) := by
    intro i
    by_cases hi : i ∈ rows
    · obtain ⟨Bi, h1, h2, h3⟩ :=
        restrictedSumset_covers hin (hp i hi) (A i) (h i) (hh i hi) (hlong i hi) (r i)
      exact ⟨Bi, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun hcon => absurd hcon hi⟩
  choose B hB using key
  exact ⟨B, fun i hi => hB i hi⟩

/-! ## 3.  Trace preservation (kernel) -/

/-- A completion supported on the middle coordinates leaves the frozen core/top trace untouched. -/
theorem completion_preserves_trace {frozen mid : Finset ℕ} (hdisj : Disjoint frozen mid)
    (ε₀ ε₁ : ℕ → Bool) :
    ∀ n ∈ frozen, (fun n => if n ∈ mid then ε₁ n else ε₀ n) n = ε₀ n := by
  intro n hn
  have : n ∉ mid := Finset.disjoint_left.1 hdisj hn
  simp [this]

/-- …and realizes the chosen completion on the middle coordinates. -/
theorem completion_agrees_on_middle {mid : Finset ℕ} (ε₀ ε₁ : ℕ → Bool) :
    ∀ n ∈ mid, (fun n => if n ∈ mid then ε₁ n else ε₀ n) n = ε₁ n := by
  intro n hn
  simp [hn]

/-! ## 4.  The conditional middle-band same-trace theorem -/

/-- **CONDITIONAL-BANKED: middle band, same trace.**  Under the fixed-cardinality additive
interface, the middle rows can be completed at the prescribed cardinalities and residues *while
preserving the frozen core/top trace exactly*: the completed selection agrees with the frozen
trace on every frozen coordinate.

This theorem is **conditional**: its first hypothesis is the uninhabited interface
`RestrictedSumsetInput`.  It is not a kernel theorem and does not close the middle band. -/
theorem middleBand_sameTrace_conditional {ι : Type*} (hin : RestrictedSumsetInput)
    (rows : Finset ι) (p : ι → ℕ) (hp : ∀ i ∈ rows, (p i).Prime)
    (A : (i : ι) → Finset (ZMod (p i))) (h : ι → ℕ)
    (hh : ∀ i ∈ rows, h i ≤ (A i).card)
    (hlong : ∀ i ∈ rows, p i ≤ h i * ((A i).card - h i) + 1)
    (r : (i : ι) → ZMod (p i))
    {frozen mid : Finset ℕ} (hdisj : Disjoint frozen mid) (ε₀ ε₁ : ℕ → Bool) :
    (∃ B : (i : ι) → Finset (ZMod (p i)),
        ∀ i ∈ rows, B i ⊆ A i ∧ (B i).card = h i ∧ ∑ x ∈ B i, x = r i) ∧
      (∀ n ∈ frozen, (fun n => if n ∈ mid then ε₁ n else ε₀ n) n = ε₀ n) :=
  ⟨middleRows_completable hin rows p hp A h hh hlong r,
    completion_preserves_trace hdisj ε₀ ε₁⟩

end MiddleBand
end ResearchBankV6
end Erdos287
