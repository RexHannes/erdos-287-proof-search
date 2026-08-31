import Mathlib
import RequestProject.Erdos287.PrimeBoxNormalization3221

/-!
# V22, Phase 2 — the Ford-(7.23) → Balanced7 `ω` source adapter

`BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45`

## What this file is

The V21 audit established that the repository contains **no physical `ω_i(p)`**: the only
coefficient apparatus is the *abstract* polarisation machinery
(`Erdos287.FactorialEuler.FactorialEulerPolarization`, with a free family
`om : ℕ → Fin 7 → K`, and `Erdos287.BalancedSevenPolarization.labelledPolynomial`).
Consequently `BALANCED7-PRIMEBOX-L1-NORMALIZATION45` was left `SOURCE_OPEN`.

This file banks the *first candidate source dictionary* for closing that gap: the
Ford-(7.23) coefficient family, presented as an **adapter interface** that would identify
the physical Balanced7 slots `ω_i` with the Ford coefficients and, in doing so, supply

* literal prime support of each box,
* the pointwise normalisation `|ω_i(p)| ≤ 1`.

## Safety

The adapter is a `structure` with no constructor application anywhere in the project: it is
**uninhabited**.  Nothing here proves that the Ford family *is* the Balanced7 family; that
is exactly the transcription obligation the interface names.

## Provenance warning

A later source forensics pass (SP-2) concluded that the Ford-(7.23) family is **not** the
literal Balanced7 source dictionary, and retracted this adapter *as the controlling
source*.  It is deliberately **not deleted**: it remains banked as historical candidate
provenance, and the retraction is recorded as machine status data in the SP-2 status
module.  See `Erdos287.SP2Status`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V22Ford

open Erdos287.V21PrimeBox

/-! ## §1. The candidate source dictionary -/

/-- Pure data for a candidate coefficient dictionary: for each of the seven Balanced7
slots, a coefficient function coming from the external source, together with the
prime cell it is supported on. -/
structure Ford723CoefficientData where
  /-- The seven candidate source coefficients. -/
  coeff : Fin 7 → ℕ → ℂ
  /-- The seven candidate source cells. -/
  cell : Fin 7 → Finset ℕ

/-- The physical prime-box datum induced by a candidate dictionary. -/
def toPrimeBoxData (F : Ford723CoefficientData) : PrimeBoxData where
  omega := F.coeff
  box := F.cell

@[simp] theorem toPrimeBoxData_omega (F : Ford723CoefficientData) :
    (toPrimeBoxData F).omega = F.coeff := rfl

@[simp] theorem toPrimeBoxData_box (F : Ford723CoefficientData) :
    (toPrimeBoxData F).box = F.cell := rfl

/-! ## §2. The adapter interface (UNINHABITED) -/

/-- **`BalancedSevenOmegaFord723Adapter3221`** — `SOURCE_OPEN / UNINHABITED`.

The transcription obligation: the physical Balanced7 slot `ω_i` *is* the Ford-(7.23)
coefficient `F.coeff i`, on the Ford cell `F.cell i`, which is literally a set of primes,
and the Ford coefficients are pointwise bounded by `1`.

Supplying an inhabitant is a **source** act (reading the physical packet), not an analytic
one.  This project supplies none. -/
structure BalancedSevenOmegaFord723Adapter3221
    (F : Ford723CoefficientData) (Dat : PrimeBoxData) : Prop where
  /-- The slot-by-slot dictionary identity for the coefficients. -/
  omega_eq : ∀ (i : Fin 7) (p : ℕ), Dat.omega i p = F.coeff i p
  /-- The slot-by-slot dictionary identity for the boxes. -/
  box_eq : ∀ i : Fin 7, Dat.box i = F.cell i
  /-- The Ford cells are literally supported on primes. -/
  cell_prime : ∀ (i : Fin 7), ∀ p ∈ F.cell i, Nat.Prime p
  /-- The Ford pointwise normalisation `|ω_i(p)| ≤ 1`. -/
  coeff_norm_le_one : ∀ (i : Fin 7) (p : ℕ), ‖F.coeff i p‖ ≤ 1

/-- **`ford723Adapter_transfers_prime_support`.**  `LEAN_PROVED` (conditional).

Given the adapter, the physical boxes are prime-supported. -/
theorem ford723Adapter_transfers_prime_support
    {F : Ford723CoefficientData} {Dat : PrimeBoxData}
    (h : BalancedSevenOmegaFord723Adapter3221 F Dat) :
    ∀ (i : Fin 7), ∀ p ∈ Dat.box i, Nat.Prime p := by
  intro i p hp
  rw [h.box_eq i] at hp
  exact h.cell_prime i p hp

/-- **`ford723Adapter_transfers_pointwise`.**  `LEAN_PROVED` (conditional).

Given the adapter, the physical coefficients obey the pointwise law with `C_ptw = 1`. -/
theorem ford723Adapter_transfers_pointwise
    {F : Ford723CoefficientData} {Dat : PrimeBoxData}
    (h : BalancedSevenOmegaFord723Adapter3221 F Dat) :
    ∀ (i : Fin 7) (p : ℕ), ‖Dat.omega i p‖ ≤ 1 := by
  intro i p
  rw [h.omega_eq i p]
  exact h.coeff_norm_le_one i p

/-! ## §3. Non-vacuity -/

/-- **`ford723Adapter_not_automatic`.**  `LEAN_PROVED`.

The adapter is a genuine restriction: explicit data refute it, so no compiler can
manufacture it. -/
theorem ford723Adapter_not_automatic :
    ∃ (F : Ford723CoefficientData) (Dat : PrimeBoxData),
      ¬ BalancedSevenOmegaFord723Adapter3221 F Dat := by
  refine ⟨⟨fun _ _ => 2, fun _ => ∅⟩, ⟨fun _ _ => 2, fun _ => ∅⟩, ?_⟩
  intro h
  have h1 := h.coeff_norm_le_one 0 0
  simp only [Complex.norm_ofNat] at h1
  norm_num at h1

/-- **`ford723Adapter_is_not_a_proof_of_the_source`.**  `LEAN_PROVED`.

Having the adapter as a hypothesis proves nothing about the physical packet on its own:
the statement below is the *identity map* on the hypothesis, recorded so that no reader
mistakes `ford723Adapter_transfers_*` for a source theorem. -/
theorem ford723Adapter_is_not_a_proof_of_the_source
    (F : Ford723CoefficientData) (Dat : PrimeBoxData) :
    BalancedSevenOmegaFord723Adapter3221 F Dat →
      BalancedSevenOmegaFord723Adapter3221 F Dat :=
  id

end V22Ford
end Erdos287
