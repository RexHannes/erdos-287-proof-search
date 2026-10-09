import Mathlib

/-!
# Anchored V3 — support size / multiplicity interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Only the **finite / combinatorial skeleton** of the later support-size theorem is formalised.

Abstract data: a finite index set of rows; each row `r` has a finite set of Boolean row choices
`ch r`, a row modulus `z r`, and a value map `val r`.  The row fibre counts are

```
N_r(t) = # { c ∈ ch r : val r c % z r = t }.
```

`UniformRowFibreBound d B` is the *hypothesis* that `N_r(t) ≤ B r` for all `r, t`.  Under it we
prove the purely finite implications:

* fixing an integer output `w` fixes the required residue in every row
  (hypothesis `ResidueDetermined`);
* hence the number of Boolean matrices producing one fixed `w` is at most `∏_r B r`;
* hence the number of distinct attainable outputs is at least
  (number of globally neutral matrices) `/ ∏_r B r`.

## OPEN analytic owner

`AsymptoticUniformRowFibres` names the analytic (Croot/Fourier-type) input that would *supply*
a uniform row-fibre bound.  It is **not** inhabited here, and its asymptotic proof is not
formalised.  Likewise the source-side conclusion `log |support| = (1 + o(1)) √M` remains
external and OPEN: nothing in this file asserts it.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3

/-- Abstract finite row data for the support/multiplicity skeleton. -/
structure RowFibreData (ι : Type*) where
  /-- the finite set of Boolean row choices of each row -/
  ch : ι → Finset ℕ
  /-- the row modulus -/
  z : ι → ℕ
  /-- the value of a row choice -/
  val : ι → ℕ → ℕ

namespace RowFibreData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (d : RowFibreData ι)

/-- The fibre of row `r` over the residue `t`. -/
def fibre (r : ι) (t : ℕ) : Finset ℕ := (d.ch r).filter (fun c => d.val r c % d.z r = t)

/-- The finite hypothesis supplying an explicit upper bound for every row fibre count. -/
def UniformRowFibreBound (B : ι → ℕ) : Prop := ∀ r t, (d.fibre r t).card ≤ B r

/-- The finite set of Boolean matrices (one choice per row). -/
def matrices : Finset (ι → ℕ) := Fintype.piFinset d.ch

/-- The hypothesis that a fixed integer output fixes the required residue in every row. -/
def ResidueDetermined (out : (ι → ℕ) → ℕ) (res : ℕ → ι → ℕ) : Prop :=
  ∀ c ∈ d.matrices, ∀ r : ι, d.val r (c r) % d.z r = res (out c) r

/-- **Fixing the output bounds the multiplicity by the product of the row fibre bounds.** -/
theorem card_fiber_le_prod {out : (ι → ℕ) → ℕ} {res : ℕ → ι → ℕ} {B : ι → ℕ}
    (hres : d.ResidueDetermined out res) (hB : d.UniformRowFibreBound B) (w : ℕ) :
    (d.matrices.filter (fun c => out c = w)).card ≤ ∏ r : ι, B r := by
  classical
  have hsub : d.matrices.filter (fun c => out c = w) ⊆
      Fintype.piFinset (fun r => d.fibre r (res w r)) := by
    intro c hc
    simp only [Finset.mem_filter] at hc
    obtain ⟨hcm, hcw⟩ := hc
    refine Fintype.mem_piFinset.mpr ?_
    intro r
    have hval := hres c hcm r
    rw [hcw] at hval
    have hcr : c r ∈ d.ch r := Fintype.mem_piFinset.mp hcm r
    exact Finset.mem_filter.mpr ⟨hcr, hval⟩
  calc (d.matrices.filter (fun c => out c = w)).card
      ≤ (Fintype.piFinset (fun r => d.fibre r (res w r))).card := Finset.card_le_card hsub
    _ = ∏ r : ι, (d.fibre r (res w r)).card := Fintype.card_piFinset _
    _ ≤ ∏ r : ι, B r := Finset.prod_le_prod' (fun r _ => hB r (res w r))

/-- **Support lower bound.**  Dividing the number of globally neutral Boolean matrices by the
maximal output multiplicity bounds the number of distinct attainable integer outputs from
below. -/
theorem card_image_ge {out : (ι → ℕ) → ℕ} {res : ℕ → ι → ℕ} {B : ι → ℕ}
    (hres : d.ResidueDetermined out res) (hB : d.UniformRowFibreBound B)
    (GN : Finset (ι → ℕ)) (hGN : GN ⊆ d.matrices) :
    GN.card / (∏ r : ι, B r) ≤ (GN.image out).card := by
  classical
  have hfib : ∀ w ∈ GN.image out, (GN.filter (fun c => out c = w)).card ≤ ∏ r : ι, B r := by
    intro w _
    refine le_trans (Finset.card_le_card ?_) (d.card_fiber_le_prod hres hB w)
    exact Finset.filter_subset_filter _ hGN
  have hmain : GN.card ≤ (∏ r : ι, B r) * (GN.image out).card :=
    Finset.card_le_mul_card_image GN _ hfib
  exact Nat.div_le_of_le_mul hmain

/-- **OPEN analytic owner.**  The uniform row-fibre estimate: every row fibre carries at most a
constant multiple of its average share `#(ch r) / z r`.  This is the Croot/Fourier-type analytic
input; it is *not* proved here and must not be assumed elsewhere in the project. -/
def AsymptoticUniformRowFibres (C : ℚ) : Prop :=
  ∀ (r : ι) (t : ℕ), ((d.fibre r t).card : ℚ) ≤ C * ((d.ch r).card : ℚ) / (d.z r : ℚ)

omit [Fintype ι] [DecidableEq ι] in
/-- If the OPEN analytic estimate is ever supplied, it yields the finite hypothesis used by the
combinatorial skeleton, with the explicit ceiling bound. -/
theorem uniformRowFibreBound_of_asymptotic {C : ℚ}
    (h : d.AsymptoticUniformRowFibres C) :
    d.UniformRowFibreBound (fun r => ⌈C * ((d.ch r).card : ℚ) / (d.z r : ℚ)⌉₊) := by
  intro r t
  have h1 := h r t
  have h2 : ⌈((d.fibre r t).card : ℚ)⌉₊ ≤ ⌈C * ((d.ch r).card : ℚ) / (d.z r : ℚ)⌉₊ :=
    Nat.ceil_le_ceil h1
  simpa using h2

end RowFibreData

end AnchoredV3
end Erdos287
