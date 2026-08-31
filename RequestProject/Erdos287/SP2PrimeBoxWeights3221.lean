import Mathlib
import RequestProject.Erdos287.SP2DirectSourceAdapter3221
import RequestProject.Erdos287.PrimeBoxL1Normalization3221
import RequestProject.Erdos287.OuterTwoPrimeBlock3221

/-!
# SP-2, Phase 2 — the literal prime-box weights `V_{i,λ}`

`BALANCED7-PRIMEBOX-L1-NORMALIZATION45` — the SP-2 treatment.

## What is new relative to V21/V22

V21 recorded that the repository has **no** physical `ω_i(p)`, and V22 offered the
Ford-(7.23) family as a candidate in which the pointwise law `|ω_i(p)| ≤ 1` was an
*assumed field*.  The SP-2 packet is different: its coefficient in slot `i` is the
**normalised prime indicator of the fixed smooth cell** `λ_i`,

```
V_{i,λ}(p) = 1  if p ∈ λ_i,   0 otherwise,
```

so the pointwise bound `|ω_i(p)| ≤ 1` is a **theorem** (`sp2Omega_norm_le_one`), not an
interface field.  What remains external is only

* the *source identification* of the physical slot with `V_{i,λ}`
  (`BalancedSevenOmegaSP2DirectSourceAdapter3221`, uninhabited, `SOURCE_OPEN`), and
* the *prime count* `#λ_i ≤ C₁ Y/log Y` (external analytic input, uninhabited).

The `L¹` compiler `sp2_primeBoxL1_of_adapter` combines the two; it has no inhabitant.

## Ownership

The SP-2 assignment of the seven prime boxes to the outer two-prime block and the inner
five-box transform is re-derived here from the V21 partition, so that no prime density is
charged twice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SP2PrimeBox

open Erdos287.SP2Source
open Erdos287.V21PrimeBox
open Erdos287.V21Outer
open Erdos287.V22PrimeBoxL1

/-! ## §1. The literal SP-2 coefficient -/

/-- **`sp2Omega`** — the literal SP-2 prime-box weight `V_{i,λ}`: the indicator of the
fixed smooth cell `λ_i`. -/
noncomputable def sp2Omega (C : SP2FixedCertificateData) (i : Fin 7) (p : ℕ) : ℂ :=
  if p ∈ C.lam i then 1 else 0

/-- **`sp2Omega_norm_le_one`.**  `LEAN_PROVED`.

The pointwise normalisation `|ω_i(p)| ≤ 1` is a *theorem* for the SP-2 weight. -/
theorem sp2Omega_norm_le_one (C : SP2FixedCertificateData) (i : Fin 7) (p : ℕ) :
    ‖sp2Omega C i p‖ ≤ 1 := by
  unfold sp2Omega
  split <;> simp

/-- Off the cell the weight vanishes: the box is literally the support. -/
theorem sp2Omega_eq_zero_of_not_mem {C : SP2FixedCertificateData} {i : Fin 7} {p : ℕ}
    (h : p ∉ C.lam i) : sp2Omega C i p = 0 := by
  unfold sp2Omega
  simp [h]

/-- On the cell the weight is exactly `1`: the normalisation is *fixed*, with no free
scalar that could hide a `log` factor. -/
theorem sp2Omega_eq_one_of_mem {C : SP2FixedCertificateData} {i : Fin 7} {p : ℕ}
    (h : p ∈ C.lam i) : sp2Omega C i p = 1 := by
  unfold sp2Omega
  simp [h]

/-- The SP-2 prime-box datum. -/
noncomputable def sp2PrimeBoxData (C : SP2FixedCertificateData) : PrimeBoxData where
  omega := sp2Omega C
  box := C.lam

@[simp] theorem sp2PrimeBoxData_omega (C : SP2FixedCertificateData) :
    (sp2PrimeBoxData C).omega = sp2Omega C := rfl

@[simp] theorem sp2PrimeBoxData_box (C : SP2FixedCertificateData) :
    (sp2PrimeBoxData C).box = C.lam := rfl

/-- The `L¹` mass of the SP-2 weight over its own cell is exactly the cell cardinality:
no hidden inflation, and nothing to estimate beyond the prime count. -/
theorem sp2Omega_l1_eq_card (C : SP2FixedCertificateData) (i : Fin 7) :
    ∑ p ∈ C.lam i, ‖sp2Omega C i p‖ = ((C.lam i).card : ℝ) := by
  rw [Finset.sum_congr rfl (fun p hp => by rw [sp2Omega_eq_one_of_mem hp])]
  simp

/-! ## §2. The SP-2 direct source adapter (SOURCE_OPEN) -/

/-- **`BalancedSevenOmegaSP2DirectSourceAdapter3221`** — `SOURCE_OPEN / UNINHABITED`.

`BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45`.  The remaining transcription obligation:
the physical Balanced7 slot `ω_i` *is* the SP-2 weight `V_{i,λ}` on the fixed smooth cell.

Note what is **not** a field here: the pointwise bound.  Once the identification is made,
`|ω_i(p)| ≤ 1` is proved, not assumed.  This is the whole content of the SP-2 repair. -/
structure BalancedSevenOmegaSP2DirectSourceAdapter3221
    (C : SP2FixedCertificateData) (Dat : PrimeBoxData) : Prop where
  /-- The SP-2 metadata normalisation holds for the certificate. -/
  packet : SP2PacketNormalization C
  /-- The slot-by-slot identification of the coefficients. -/
  omega_eq : ∀ (i : Fin 7) (p : ℕ), Dat.omega i p = sp2Omega C i p
  /-- The slot-by-slot identification of the boxes. -/
  box_eq : ∀ i : Fin 7, Dat.box i = C.lam i

/-- Given the SP-2 adapter, the pointwise law holds with constant `1` — **proved**. -/
theorem sp2Adapter_pointwise {C : SP2FixedCertificateData} {Dat : PrimeBoxData}
    (h : BalancedSevenOmegaSP2DirectSourceAdapter3221 C Dat) :
    ∀ (i : Fin 7) (p : ℕ), ‖Dat.omega i p‖ ≤ 1 := by
  intro i p
  rw [h.omega_eq i p]
  exact sp2Omega_norm_le_one C i p

/-- Given the SP-2 adapter, the boxes are prime-supported — from the metadata. -/
theorem sp2Adapter_prime_support {C : SP2FixedCertificateData} {Dat : PrimeBoxData}
    (h : BalancedSevenOmegaSP2DirectSourceAdapter3221 C Dat) :
    ∀ (i : Fin 7), ∀ p ∈ Dat.box i, Nat.Prime p := by
  intro i p hp
  rw [h.box_eq i] at hp
  exact h.packet.cell_prime i p hp

/-- **`sp2Adapter_not_automatic`.**  `LEAN_PROVED`.

The SP-2 identification is a genuine restriction: explicit data refute it. -/
theorem sp2Adapter_not_automatic :
    ∃ (C : SP2FixedCertificateData) (Dat : PrimeBoxData),
      ¬ BalancedSevenOmegaSP2DirectSourceAdapter3221 C Dat := by
  refine ⟨⟨0, ∅, 7, 3, 1, fun _ => {2}⟩, ⟨fun _ _ => 2, fun _ => ∅⟩, ?_⟩
  intro h
  have h1 := sp2Adapter_pointwise h 0 0
  simp only [Complex.norm_ofNat] at h1
  norm_num at h1

/-! ## §3. The SP-2 prime-box `L¹` compiler -/

/-- **`sp2_primeBoxL1_of_adapter`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
SP-2 source identification   (SOURCE_OPEN, uninhabited)
  + prime-box cardinality input  (external, uninhabited)
      ⇒ BALANCED7-PRIMEBOX-L1-NORMALIZATION45  with C_ptw = 1
```

Compared with the V22 (Ford) route, one antecedent has been *discharged*: the pointwise
coefficient law is now a theorem about `V_{i,λ}`. -/
theorem sp2_primeBoxL1_of_adapter
    {C : SP2FixedCertificateData} {Dat : PrimeBoxData} {C1 Y : ℝ}
    (hA : BalancedSevenOmegaSP2DirectSourceAdapter3221 C Dat)
    (hB : PrimeBoxCardinality3221Input Dat C1 Y) :
    BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y := by
  refine ⟨sp2Adapter_prime_support hA, sp2Adapter_pointwise hA, ?_⟩
  intro i
  have h := primeBoxL1_of_pointwise_and_count (om := Dat.omega i) (P := Dat.box i)
    (Cptw := 1) (K := C1 * (Y / Real.log Y)) zero_le_one
    (fun p _ => sp2Adapter_pointwise hA i p) (hB.card_bound i)
  simpa using h

/-! ## §4. SP-2 ownership of the seven prime boxes -/

/-- The SP-2 outer two-prime block: the same two labels as the V21 assignment. -/
def sp2OuterBoxes : Finset (Fin 7) := outerBoxes

/-- The SP-2 inner five-box transform. -/
def sp2InnerBoxes : Finset (Fin 7) := innerBoxes

/-- **`sp2_outerInner_disjoint`.**  `LEAN_PROVED`. -/
theorem sp2_outerInner_disjoint : Disjoint sp2OuterBoxes sp2InnerBoxes :=
  outerInnerBox_disjoint

/-- **`sp2_outerInner_cover`.**  `LEAN_PROVED`. -/
theorem sp2_outerInner_cover : sp2OuterBoxes ∪ sp2InnerBoxes = Finset.univ :=
  outerInnerBox_cover

/-- **`sp2_no_primeDensity_doubleSpend`.**  `LEAN_PROVED`.

Each of the seven SP-2 prime boxes is owned by exactly one of the two blocks, so the
`Y/log Y` density of a box is charged exactly once. -/
theorem sp2_no_primeDensity_doubleSpend (i : Fin 7) :
    (i ∈ sp2OuterBoxes ∧ i ∉ sp2InnerBoxes) ∨ (i ∈ sp2InnerBoxes ∧ i ∉ sp2OuterBoxes) :=
  primeDensity_no_double_spending i

/-- The SP-2 block sizes: two outer, five inner. -/
theorem sp2_block_cardinalities :
    sp2OuterBoxes.card = 2 ∧ sp2InnerBoxes.card = 5 ∧
      sp2OuterBoxes.card + sp2InnerBoxes.card = 7 :=
  sevenBox_partition_cardinality

end SP2PrimeBox
end Erdos287
