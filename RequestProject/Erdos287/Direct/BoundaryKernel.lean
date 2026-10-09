import RequestProject.Erdos287.Direct.Core
import RequestProject.Erdos287.TopLayer

/-!
# Route D — the finite boundary-kernel API

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The boundary kernel is the finite high-valuation part of a hypothetical selection.  It is kept
strictly separated into

* **kernel variables** (the positions the kernel controls);
* **forced-zero pins** (positions that must be omitted);
* **forced-positive pins** (positions that must be selected);
* **feasibility** (existence of a mask obeying the pins and the local no-two-omissions rule);
* **top prime-power congruences** (imported from the elementary package, as a proved bridge).

The deterministic part — necessary conditions on the pins, the forced neighbours of a pinned
omission, and the *restriction* half of the extension/restriction bridge — is kernel-proved
here.  The *extension* half is genuinely an asymptotic/analytic statement and is therefore kept
as an explicit named interface proposition (`KernelExtensionInterface`), consumed by a
conditional bridge and never asserted.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.25  Kernel data and feasibility -/

/-- Finite boundary-kernel data on the ambient interval `[a, M]`. -/
structure KernelData where
  /-- the positions the kernel controls -/
  vars : Finset ℕ
  /-- positions pinned to be omitted -/
  forcedZero : Finset ℕ
  /-- positions pinned to be selected -/
  forcedOne : Finset ℕ

/-- A mask realises the kernel data. -/
def Realises (K : KernelData) (a M : ℕ) (eps : ℕ → Bool) : Prop :=
  (∀ n ∈ K.forcedZero, eps n = false) ∧ (∀ n ∈ K.forcedOne, eps n = true) ∧
    NoTwoConsecutiveOmissions a M eps

/-- The kernel data is feasible on `[a, M]`. -/
def Feasible (K : KernelData) (a M : ℕ) : Prop := ∃ eps : ℕ → Bool, Realises K a M eps

/-- **`feasible_pins_disjoint`.**  `KERNEL-PROVED`.  A feasible kernel cannot pin a position
both ways. -/
theorem feasible_pins_disjoint {K : KernelData} {a M : ℕ} (h : Feasible K a M) :
    Disjoint K.forcedZero K.forcedOne := by
  obtain ⟨eps, hz, ho, -⟩ := h
  rw [Finset.disjoint_left]
  intro n hn hn'
  have := hz n hn
  rw [ho n hn'] at this
  exact absurd this (by simp)

/-- **`feasible_forcedZero_nonadjacent`.**  `KERNEL-PROVED`.  A feasible kernel never pins two
adjacent positions of the window to zero. -/
theorem feasible_forcedZero_nonadjacent {K : KernelData} {a M : ℕ} (h : Feasible K a M)
    {n : ℕ} (hlo : a ≤ n) (hhi : n + 1 ≤ M)
    (h1 : n ∈ K.forcedZero) (h2 : n + 1 ∈ K.forcedZero) : False := by
  obtain ⟨eps, hz, -, hiso⟩ := h
  rcases hiso n hlo hhi with hc | hc
  · rw [hz n h1] at hc; exact absurd hc (by simp)
  · rw [hz (n + 1) h2] at hc; exact absurd hc (by simp)

/-- **`feasible_forces_neighbours`.**  `KERNEL-PROVED`.  Every realisation of a kernel with an
interior forced-zero pin selects both neighbours: the pins propagate deterministically. -/
theorem feasible_forces_neighbours {K : KernelData} {a M : ℕ} {eps : ℕ → Bool}
    (h : Realises K a M eps) {n : ℕ} (hlo : a < n) (hhi : n < M) (hn : n ∈ K.forcedZero) :
    eps (n - 1) = true ∧ eps (n + 1) = true :=
  neighbours_selected_of_omitted h.2.2 hlo hhi (h.1 n hn)

/-! ## D.26  Restriction (deterministic) and extension (interface) -/

/-- **`realises_restrict`.**  `KERNEL-PROVED`.  Restriction is deterministic: a realisation on
a window restricts to any subwindow, after restricting the pins. -/
theorem realises_restrict {K : KernelData} {a M a' M' : ℕ} {eps : ℕ → Bool}
    (h : Realises K a M eps) (h1 : a ≤ a') (h2 : M' ≤ M) :
    Realises { vars := K.vars.filter (fun n => a' ≤ n ∧ n ≤ M'),
               forcedZero := K.forcedZero.filter (fun n => a' ≤ n ∧ n ≤ M'),
               forcedOne := K.forcedOne.filter (fun n => a' ≤ n ∧ n ≤ M') } a' M' eps := by
  refine ⟨fun n hn => h.1 n (Finset.mem_of_mem_filter _ hn),
    fun n hn => h.2.1 n (Finset.mem_of_mem_filter _ hn), ?_⟩
  intro n hlo hhi
  exact h.2.2 n (le_trans h1 hlo) (le_trans hhi h2)

/-- **`feasible_restrict`.**  `KERNEL-PROVED`.  Feasibility is inherited by subwindows. -/
theorem feasible_restrict {K : KernelData} {a M a' M' : ℕ} (h : Feasible K a M)
    (h1 : a ≤ a') (h2 : M' ≤ M) :
    Feasible { vars := K.vars.filter (fun n => a' ≤ n ∧ n ≤ M'),
               forcedZero := K.forcedZero.filter (fun n => a' ≤ n ∧ n ≤ M'),
               forcedOne := K.forcedOne.filter (fun n => a' ≤ n ∧ n ≤ M') } a' M' := by
  obtain ⟨eps, heps⟩ := h
  exact ⟨eps, realises_restrict heps h1 h2⟩

/-- **Interface (open).**  Extension of a feasible boundary kernel to a *completed* selection
with prescribed reciprocal value.  This is the asymptotic/analytic half of the kernel bridge:
it is a named hypothesis, never an axiom, and it is **not** inhabited anywhere. -/
def KernelExtensionInterface (K : KernelData) (a M : ℕ) : Prop :=
  ∀ eps : ℕ → Bool, Realises K a M eps →
    ∃ eps' : ℕ → Bool, Realises K a M eps' ∧ EndpointSelected a M eps' ∧
      recipSum (selected a M eps') = 1

/-- **`directCounterexample_of_kernelExtension`.**  `KERNEL-PROVED` bridge, `CONDITIONAL` on
the extension interface: a feasible kernel plus the interface produces a Route-D
counterexample.  Nothing here proves the interface. -/
theorem directCounterexample_of_kernelExtension {K : KernelData} {a M : ℕ}
    (ha : 1 < a) (haM : a < M) (hfeas : Feasible K a M)
    (hext : KernelExtensionInterface K a M) :
    ∃ eps : ℕ → Bool, DirectCounterexample a M eps := by
  obtain ⟨eps, heps⟩ := hfeas
  obtain ⟨eps', hreal, hend, hsum⟩ := hext eps heps
  exact ⟨eps', ⟨ha, haM, hend, hreal.2.2, hsum⟩⟩

/-! ## D.27  Top prime-power congruences of the selected set

These are *proved* consequences of the elementary package, imported into Route D as bridges. -/

/-- **`direct_topLayer_congruence`.**  `KERNEL-PROVED` bridge.  The top `p`-adic layer of the
selected set of a Route-D counterexample satisfies the cofactor congruence. -/
theorem direct_topLayer_congruence {a M : ℕ} {eps : ℕ → Bool} (h : DirectCounterexample a M eps)
    {p : ℕ} (hp : p.Prime) (he : 1 ≤ topExp (selected a M eps) p) :
    (∑ x ∈ topLayer (selected a M eps) p, (((ordCompl[p] x : ℕ) : ZMod p))⁻¹) = 0 := by
  refine topLayer_congruence (selected a M eps) p hp ?_ h.sum_one he
  intro n hn
  have hlo := (mem_selected.1 hn).1.1
  have ha := h.one_lt
  omega

/-- **`direct_topLayer_card_ne_one`.**  `KERNEL-PROVED` bridge.  The top layer of a Route-D
counterexample is never a singleton. -/
theorem direct_topLayer_card_ne_one {a M : ℕ} {eps : ℕ → Bool} (h : DirectCounterexample a M eps)
    {p : ℕ} (hp : p.Prime) (he : 1 ≤ topExp (selected a M eps) p) :
    (topLayer (selected a M eps) p).card ≠ 1 := by
  refine topLayer_card_ne_one (selected a M eps) p hp ?_ h.sum_one he
  intro n hn
  have hlo := (mem_selected.1 hn).1.1
  have ha := h.one_lt
  omega

end Direct
end Erdos287
