import Mathlib
import RequestProject.Erdos287.SmallQSmallRAdapters3221
import RequestProject.CurrentProgramme.ThreePlusFourProductAlgebra

/-!
# CurrentProgramme §5–§6 — retiring the Type-I SmallQ provider, and the `3+4` source socket

`AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45` :
`SUPERSEDED AS CONTROLLING FRONTIER / SOURCE MISMATCH / NOT FALSE`.

The historical V24 module `SmallQSmallRAdapters3221` is **not modified**; its interface stays
exactly as banked.  What is added here is the routing record explaining why that interface is
no longer the controlling frontier:

* the divisor `q` in the packet divides the *affine* value `2P + s`, not `P`
  (`smallQ_source_mismatch`, `dvd_shift_of_dvd_affine_and_base`), so a generic Gate-0 Type-I
  input keyed on `P` is the wrong provider;
* the supersession is a **routing** statement: no refutation of the old interface is claimed
  here, and none is banked.

`AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45` — the **first exact residual**.  The replacement
provider is the `3 + 4` multiplicative large sieve, whose literal obligations are recorded in
the uninhabited socket `BalancedSevenSmallQ34LSInput`.  That socket is *not* inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §5.1  The source mismatch -/

/-- **`dvd_shift_of_dvd_affine_and_base`.**  `LEAN_PROVED`.

If `q` divides both the affine value `2P + s` and the base `P`, then `q` divides the shift
`s`.  For a generic shift this fails, which is the exact reason the packet's `q` variable is
not keyed on `P`. -/
theorem dvd_shift_of_dvd_affine_and_base {q P s : ℕ} (h1 : q ∣ 2 * P + s) (h2 : q ∣ P) :
    q ∣ s := by
  have h3 : q ∣ 2 * P := h2.mul_left 2
  have h4 : s = 2 * P + s - 2 * P := by omega
  rw [h4]
  exact Nat.dvd_sub h1 h3

/-- **`smallQ_source_mismatch`.**  `LEAN_PROVED`.

The divisor variable of the packet divides `2P + s`, and need not divide `P`:
`7 ∣ 2·3 + 1` but `7 ∤ 3`.  Hence a Type-I input keyed on the modulus of `P` is the wrong
provider for this packet. -/
theorem smallQ_source_mismatch : ∃ P s q : ℕ, q ∣ (2 * P + s) ∧ ¬ q ∣ P := by
  refine ⟨3, 1, 7, ?_, ?_⟩ <;> decide

/-- The two candidate providers for the SmallQ sector. -/
inductive SmallQRoute
  | typeIAdapterSuperseded
  | multiplicativeLargeSieve34
  deriving DecidableEq, Fintype, Repr

/-- The controlling SmallQ provider after the audit. -/
def controllingSmallQRoute : SmallQRoute := SmallQRoute.multiplicativeLargeSieve34

/-- **`smallQ_route_superseded`.**  `LEAN_PROVED` (bookkeeping).

The controlling route is the `3 + 4` multiplicative large sieve, which is *not* the
superseded Type-I adapter route. -/
theorem smallQ_route_superseded :
    controllingSmallQRoute = SmallQRoute.multiplicativeLargeSieve34 ∧
      controllingSmallQRoute ≠ SmallQRoute.typeIAdapterSuperseded := by
  constructor
  · rfl
  · decide

/-- **`smallQ_supersession_is_not_refutation`.**  `LEAN_PROVED`.

Supersession is a routing statement.  What *is* banked about the old interface is only the
V24 fact that it is not automatic; no proof of its negation for the physical data is claimed
here, and none is used. -/
theorem smallQ_supersession_is_not_refutation :
    controllingSmallQRoute ≠ SmallQRoute.typeIAdapterSuperseded ∧
      (∃ (u N : ℕ) (coeff : ℕ × ℕ → ℝ) (qRange rRange : Finset ℕ) (sgn : ℤ)
        (s : Erdos287.Vaughan.AffineSign) (targetNorm : ℝ) (provider : V24FullQ.Provider),
        ¬ V24Adapters.Affine287SP2SmallQTypeIAdapterInput u N coeff qRange rRange sgn s
          targetNorm provider) :=
  ⟨smallQ_route_superseded.2, V24Adapters.smallQAdapter_not_automatic⟩

/-! ## §6  The `3 + 4` multiplicative large-sieve source socket -/

/-- **`BalancedSevenSmallQ34LSInput`** — `EXTERNAL / SOURCE OPEN / UNINHABITED`.

The literal obligations of the replacement SmallQ provider.  Every field is an obligation on
*given* data; the structure is never inhabited in this repository.

The parameters are: the prime box `S` and output range `N`, the labelled `3` and `4` weight
families `w3`, `w4`, the realised coefficients `A3`, `B4`, the `q`-range `qRange`, the affine
data `(P, s)`, the multiplicity constants, the `L²` constants, the `q/φ(q)` constant, the
scale `X` with the final saving `eps`, and three `Prop`-valued source children:
imprimitive-to-primitive conductor bookkeeping, Mellin separation, the tiny-modulus
Siegel–Walfisz child and the `3+4` multiplicative-large-sieve child. -/
structure BalancedSevenSmallQ34LSInput
    (S N qRange : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ)
    (A3 B4 : ℕ → ℝ) (P s : ℕ) (mult3 mult4 : ℕ) (E3 E4 Cqphi Clog X eps : ℝ)
    (conductorBookkeeping mellinSeparation siegelWalfischChild largeSieveChild : Prop) :
    Prop where
  /-- SP-2 prime-box weights: the box consists of primes and the weights are normalised. -/
  sp2_prime_box : (∀ p ∈ S, Nat.Prime p) ∧ (∀ i p, |w3 i p| ≤ 1) ∧ (∀ i p, |w4 i p| ≤ 1)
  /-- The three-prime coefficient is the labelled convolution `a₃`. -/
  a3_coefficient : ∀ n, A3 n = a3 S w3 n
  /-- The four-prime coefficient is the labelled convolution `b₄`. -/
  b4_coefficient : ∀ m, B4 m = b4 S w4 m
  /-- `L²` coefficient norms. -/
  l2_norms : (∑ n ∈ N, (A3 n) ^ 2 ≤ E3) ∧ (∑ m ∈ N, (B4 m) ^ 2 ≤ E4)
  /-- Labelled-product multiplicity constants, valid on the declared range. -/
  labelled_multiplicity :
    representationMultiplicity 3 S N ≤ mult3 ∧ representationMultiplicity 4 S N ≤ mult4
  /-- Repeated primes are *included*: no injectivity is assumed on labelled tuples. -/
  repeated_primes : ∀ (n : ℕ) (t : Fin 3 → ℕ), (∀ i, t i ∈ S) → (∏ i, t i) = n →
    t ∈ prodFiber 3 S n
  /-- Imprimitive-to-primitive conductor bookkeeping (external child). -/
  conductor_bookkeeping : conductorBookkeeping
  /-- The `q/φ(q)` factor is controlled on the declared `q`-range. -/
  q_over_phi : ∀ q ∈ qRange, (q : ℝ) / (Nat.totient q : ℝ) ≤ Cqphi
  /-- Mellin separation of the `q` and `r` variables (external child). -/
  mellin_separation : mellinSeparation
  /-- The literal `log((2P+s)/q)` factor is controlled on the declared `q`-range. -/
  log_factor : ∀ q ∈ qRange, |Real.log (((2 * P + s : ℕ) : ℝ) / q)| ≤ Clog
  /-- Tiny-modulus Siegel–Walfisz child (external). -/
  siegel_walfisz : siegelWalfischChild
  /-- `3+4` multiplicative-large-sieve child (external). -/
  large_sieve : largeSieveChild
  /-- The scale is nontrivial and the declared saving is genuine. -/
  scale : 3 ≤ X ∧ 0 < eps
  /-- The final `o(X / log X)` target for the SmallQ sector sum. -/
  final_target : |V24Adapters.sigmaSmallQ ⌊X⌋₊ (2 * P + s) (fun _ => 0)| ≤
    eps * X / Real.log X

/-- **`smallQ34LS_consumer`** — `CONDITIONAL`.

If the socket is ever supplied, the SmallQ sector meets the declared `o(X/log X)` target and
the coefficients are the labelled `3+4` convolutions. -/
theorem smallQ34LS_consumer
    {S N qRange : Finset ℕ} {w3 : Fin 3 → ℕ → ℝ} {w4 : Fin 4 → ℕ → ℝ}
    {A3 B4 : ℕ → ℝ} {P s mult3 mult4 : ℕ} {E3 E4 Cqphi Clog X eps : ℝ}
    {cb ms swc lsc : Prop}
    (h : BalancedSevenSmallQ34LSInput S N qRange w3 w4 A3 B4 P s mult3 mult4 E3 E4 Cqphi
      Clog X eps cb ms swc lsc) :
    (∀ n, A3 n = a3 S w3 n) ∧
      |V24Adapters.sigmaSmallQ ⌊X⌋₊ (2 * P + s) (fun _ => 0)| ≤ eps * X / Real.log X :=
  ⟨h.a3_coefficient, h.final_target⟩

/-- **`smallQ34LS_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction — explicit data refute it — and it is not inhabited. -/
theorem smallQ34LS_not_automatic :
    ∃ (S N qRange : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ)
      (A3 B4 : ℕ → ℝ) (P s mult3 mult4 : ℕ) (E3 E4 Cqphi Clog X eps : ℝ)
      (cb ms swc lsc : Prop),
      ¬ BalancedSevenSmallQ34LSInput S N qRange w3 w4 A3 B4 P s mult3 mult4 E3 E4 Cqphi
        Clog X eps cb ms swc lsc := by
  refine ⟨{4}, ∅, ∅, fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0,
    0, 0, 0, 0, 3, 1, True, True, True, True, ?_⟩
  intro h
  have := h.sp2_prime_box.1 4 (by simp)
  norm_num at this

/-- **`smallQ34LS_is_first_exact_residual`.**  `LEAN_PROVED` (bookkeeping).

The controlling SmallQ route is the `3+4` large sieve and its source socket is open; the
residual is coefficient/source *normalisation*, not exponent capacity — the exponent ledger
of §2 is already positive. -/
theorem smallQ34LS_is_first_exact_residual :
    controllingSmallQRoute = SmallQRoute.multiplicativeLargeSieve34 ∧
      (cVarCurrent - 2 * cExtCurrent = 3) ∧
      (∃ (S N qRange : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ)
        (A3 B4 : ℕ → ℝ) (P s mult3 mult4 : ℕ) (E3 E4 Cqphi Clog X eps : ℝ)
        (cb ms swc lsc : Prop),
        ¬ BalancedSevenSmallQ34LSInput S N qRange w3 w4 A3 B4 P s mult3 mult4 E3 E4 Cqphi
          Clog X eps cb ms swc lsc) :=
  ⟨rfl, logR_signed_margin.1, smallQ34LS_not_automatic⟩

end CurrentProgramme
end Erdos287
