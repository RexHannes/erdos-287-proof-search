import Mathlib
import RequestProject.Erdos287.Ford723BalancedSevenAdapter3221

/-!
# V22, Phase 3 — the prime-box `L¹` normalization compiler

`BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN` (still).

This file keeps the three logically independent ingredients of the prime-box `L¹` bound
strictly separate, so that none of them can be silently manufactured from the others:

* **(A) the source dictionary** — an inhabitant of
  `Erdos287.V22Ford.BalancedSevenOmegaFord723Adapter3221`, giving prime support and the
  pointwise law `|ω_i(p)| ≤ 1`;
* **(B) the prime-counting input** — an inhabitant of `PrimeBoxCardinality3221Input`,
  i.e. `#box_i ≤ C₁ · Y / log Y`, which is external analytic information (a
  Chebyshev/PNT-type count) and is **not** proved here;
* **(C) the purely formal `L¹` compiler** — `Erdos287.V21PrimeBox.primeBoxL1_of_pointwise_and_count`.

Only (C) is Lean-proved.  `primeBoxL1_of_ford723Adapter` combines (A) + (B) + (C) and is
therefore a **conditional compiler with no inhabitant**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V22PrimeBoxL1

open Erdos287.V21PrimeBox
open Erdos287.V22Ford

/-! ## §1. The external prime-counting input -/

/-- **`PrimeBoxCardinality3221Input`** — `EXTERNAL ANALYTIC INTERFACE / UNINHABITED`.

The prime-box cardinality input `#box_i ≤ C₁ · (Y / log Y)`.  This is the only place where
prime density is charged, and it is charged **once** (see the ownership firewall in
`Erdos287.V21Outer`). -/
structure PrimeBoxCardinality3221Input (Dat : PrimeBoxData) (C1 Y : ℝ) : Prop where
  /-- The constant is nonnegative. -/
  C1_nonneg : 0 ≤ C1
  /-- The density input, one box at a time. -/
  card_bound : ∀ i : Fin 7, ((Dat.box i).card : ℝ) ≤ C1 * (Y / Real.log Y)

/-- **`primeBoxCardinality_not_automatic`.**  `LEAN_PROVED`.

The cardinality input is a genuine restriction. -/
theorem primeBoxCardinality_not_automatic :
    ∃ (Dat : PrimeBoxData) (C1 Y : ℝ), ¬ PrimeBoxCardinality3221Input Dat C1 Y := by
  refine ⟨⟨fun _ _ => 0, fun _ => {2}⟩, 0, 1, ?_⟩
  intro h
  have h1 := h.card_bound 0
  simp at h1
  linarith

/-! ## §2. The conditional `L¹` compiler -/

/-- **`primeBoxL1_of_ford723Adapter`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
source dictionary  (A, uninhabited)
  + prime-box cardinality input  (B, uninhabited)
  + formal L¹ compiler           (C, proved)
        ⇒  BALANCED7-PRIMEBOX-L1-NORMALIZATION45  with  C_ptw = 1
```

Note the constant: the pointwise law enters with `C_ptw = 1`, so the `L¹` constant is the
prime-counting constant `C₁` itself, with no hidden inflation. -/
theorem primeBoxL1_of_ford723Adapter
    {F : Ford723CoefficientData} {Dat : PrimeBoxData} {C1 Y : ℝ}
    (hA : BalancedSevenOmegaFord723Adapter3221 F Dat)
    (hB : PrimeBoxCardinality3221Input Dat C1 Y) :
    BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y := by
  refine ⟨ford723Adapter_transfers_prime_support hA,
    ford723Adapter_transfers_pointwise hA, ?_⟩
  intro i
  have h := primeBoxL1_of_pointwise_and_count (om := Dat.omega i) (P := Dat.box i)
    (Cptw := 1) (K := C1 * (Y / Real.log Y)) zero_le_one
    (fun p _ => ford723Adapter_transfers_pointwise hA i p) (hB.card_bound i)
  simpa using h

/-! ## §3. Anti-circularity -/

/-- **`primeBoxL1_compiler_cannot_construct_cardinality`.**  `LEAN_PROVED`.

The compiler cannot manufacture its own prime-counting antecedent: there are data for
which the conclusion of the compiler is available (vacuously, on empty boxes with the zero
coefficient) while the cardinality input fails. -/
theorem primeBoxL1_compiler_cannot_construct_cardinality :
    ∃ (Dat : PrimeBoxData) (C1 Y : ℝ),
      BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y ∧
        ¬ PrimeBoxCardinality3221Input Dat C1 Y := by
  refine ⟨⟨fun _ _ => 0, fun _ => {2}⟩, 0, 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i p hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact Nat.prime_two
  · intro i p; simp
  · intro i; simp
  · intro h
    have h1 := h.card_bound 0
    simp at h1
    linarith

/-- **`primeBoxL1_not_automatic_v22`.**  `LEAN_PROVED`.

The `L¹` normalisation itself stays a genuine restriction in V22. -/
theorem primeBoxL1_not_automatic_v22 :
    ∃ (Dat : PrimeBoxData) (C1 Y : ℝ),
      ¬ BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y := by
  refine ⟨⟨fun _ _ => 1, fun _ => {2}⟩, 0, 1, ?_⟩
  intro h
  have h1 := h.l1_bound 0
  simp at h1
  linarith

end V22PrimeBoxL1
end Erdos287
