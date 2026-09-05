import RequestProject.CurrentProgramme.Erdos287September3TotFixedResidueArithmetic

/-!
# Erdős #287 — September-3 bank, §D: the conditional fixed-residue AP socket and `E_T`
compiler

```
PHYSICAL SLOT ALGEBRA (index multiplicity)   : KERNEL-PROVED
AP ANALYTIC SOCKET                           : EXTERNAL / UNINHABITED (no inhabitant built)
CONDITIONAL E_T COMPILER (implication only)  : KERNEL-PROVED
MAYNARD THEOREM 1.1                          : NOT ASSERTED, NOT REPRESENTED AS A FIELD
ENDPOINT-SUPREMUM FIELD                      : NOT BANKED
NUMERICAL E_T VALUE                          : NOT BANKED
```

This module separates the *stable source algebra* (kernel-proved, §B/§C) from the
*unstable external analysis* (a hypothesis socket which this development never inhabits).

## The socket

`PhysicalFixedResidueAPBound F` is the **only** analytic input the compiler consumes.  It
exposes, as explicit fields,

* the **residue** `s = ±1` and the **modulus** data `q1 ∈ {1, 4}`, `d` odd
  (family `0`: `q1 = 1`, modulus `d`;  family `2`: `q1 = 4`, modulus `4d`, exactly the two
  families proved in `Erdos287September3TotFixedResidueArithmetic.lean`);
* the **finite interval / endpoint** data `lo`, `hi` of each physical slot;
* the **prime discrepancy** `discrepancy` of each slot over its own finite interval;
* the **numerical error function** `err` and the bound `|discrepancy| ≤ err`;
* the **lower activation threshold** `activation`.

It does **not** contain the desired `E_T` conclusion as a field, and it does **not** contain
an endpoint-supremum field: the hypothesis is stated *per finite physical interval*, which
is the weakest form the compiler needs.  In particular no paper theorem (Maynard 1.1,
Bombieri–Vinogradov, Wright, Bordignon–Lee, …) is asserted, referenced as an axiom, or
encoded in a field.

**Honesty note.**  The socket is deliberately *weak*: nothing forces `err` to be small, so a
mathematically vacuous inhabitant with a huge `err` exists in principle.  Its content is
therefore purely that `err` is a *supplied* numerical bound; correspondingly the compiler's
output is symbolic in `err` and asserts no number.  This development constructs **no**
inhabitant of the socket.

## The compiler

`totLaneFixedResidueConditionalBound45` is a pure implication:

    PhysicalFixedResidueAPBound  →  |E_T| ≤ ∑_{slots} |w d| · err(slot),

with the slot index set `D ×ˢ {1,4} ×ˢ {−1,+1}` — so each odd modulus `d` contributes
**exactly four** slots (`slotIndex_fiber_card`): the two signs counted once and the two
parity families counted once, with no re-use of the Möbius cancellation, which has already
been consumed once and for all by the exact source pairing of §B.

**FIREWALLS.**  The conditional compiler
(i) does not assert Maynard or any other analytic theorem;
(ii) does not assert a numerical `E_T` bound;
(iii) does not assert `E_T = o(B_X)` — that would have to be supplied separately;
(iv) does not imply Erdős #287, which remains open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace September3ConditionalCompiler

/-! ## §D.1  Physical slots -/

/-- A physical fixed-residue slot: the finite interval `[lo, hi]`, the parity-family prefix
modulus `q1 ∈ {1, 4}`, the odd modulus part `d`, and the residue sign `s = ±1`.
The full AP modulus of the slot is `q1 * d` (family `0`: `d`; family `2`: `4d`). -/
structure Slot where
  /-- left endpoint of the physical interval -/
  lo : ℕ
  /-- right endpoint of the physical interval -/
  hi : ℕ
  /-- parity-family prefix modulus, `1` (family `0`) or `4` (family `2`) -/
  q1 : ℕ
  /-- odd modulus part -/
  d : ℕ
  /-- residue sign, `+1` or `−1` -/
  s : ℤ

/-- The AP modulus of a slot. -/
def Slot.modulus (S : Slot) : ℕ := S.q1 * S.d

/-- The AP residue of a slot. -/
def Slot.residue (S : Slot) : ℤ := S.s

/-- The physical slot family: the finite set `D` of odd moduli actually used, the activation
threshold, and the interval endpoints attached to each `(d, q1, s)`. -/
structure PhysicalSlotFamily where
  /-- the odd moduli in play -/
  D : Finset ℕ
  /-- every modulus in play is odd -/
  D_odd : ∀ d ∈ D, Odd d
  /-- lower activation threshold -/
  activation : ℕ
  /-- every modulus in play is above the activation threshold -/
  D_activated : ∀ d ∈ D, activation ≤ d
  /-- left endpoint of the physical interval of the slot `(d, q1, s)` -/
  lo : ℕ → ℕ → ℤ → ℕ
  /-- right endpoint of the physical interval of the slot `(d, q1, s)` -/
  hi : ℕ → ℕ → ℤ → ℕ

namespace PhysicalSlotFamily

variable (F : PhysicalSlotFamily)

/-- The slot attached to an index `(d, q1, s)`. -/
def slotOf (i : ℕ × ℕ × ℤ) : Slot :=
  ⟨F.lo i.1 i.2.1 i.2.2, F.hi i.1 i.2.1 i.2.2, i.2.1, i.1, i.2.2⟩

/-- The full slot index: each odd modulus `d ∈ D`, each parity family `q1 ∈ {1, 4}`, each
sign `s ∈ {−1, +1}` — every combination exactly once. -/
def slotIndex : Finset (ℕ × ℕ × ℤ) :=
  F.D ×ˢ (({1, 4} : Finset ℕ) ×ˢ ({-1, 1} : Finset ℤ))

/-- **`slotIndex_card`.**  `KERNEL-PROVED`.  Source interval multiplicity: `4 · |D|` slots —
two parity families times two signs, each counted once. -/
theorem slotIndex_card : (F.slotIndex).card = 4 * F.D.card := by
  simp [slotIndex, Finset.card_product, Finset.card_insert_of_notMem, mul_comm]

/-- **`slotIndex_fiber_card`.**  `KERNEL-PROVED`.  Each odd modulus `d ∈ D` carries exactly
four slots: the two signs counted once and the two parity families counted once. -/
theorem slotIndex_fiber_card {d : ℕ} (hd : d ∈ F.D) :
    ((F.slotIndex).filter (fun i => i.1 = d)).card = 4 := by
  classical
  have : (F.slotIndex).filter (fun i => i.1 = d)
      = ({d} : Finset ℕ) ×ˢ (({1, 4} : Finset ℕ) ×ˢ ({-1, 1} : Finset ℤ)) := by
    ext i
    simp only [slotIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, rfl⟩; exact ⟨rfl, h2⟩
    · rintro ⟨rfl, h2⟩; exact ⟨⟨hd, h2⟩, rfl⟩
  rw [this]
  simp [Finset.card_product]

end PhysicalSlotFamily

/-! ## §D.2  The external AP hypothesis socket (uninhabited here) -/

/-- **`PhysicalFixedResidueAPBound`** — `EXTERNAL / UNINHABITED`.

The weakest abstract AP-discrepancy hypothesis sufficient for the compiler: for each
physical slot (finite interval, modulus `q1 · d`, residue `s`) above the activation
threshold, the prime discrepancy of that slot is bounded by a supplied numerical error
function.  The hypothesis is quantified over the finite physical intervals directly; there
is no endpoint-supremum field, and no paper theorem is named or assumed.

This development constructs no inhabitant of this structure. -/
structure PhysicalFixedResidueAPBound (F : PhysicalSlotFamily) where
  /-- the prime discrepancy of a slot over its own finite interval -/
  discrepancy : Slot → ℝ
  /-- the supplied numerical error function -/
  err : Slot → ℝ
  /-- the error function is nonnegative on the slots in play -/
  err_nonneg : ∀ i ∈ F.slotIndex, 0 ≤ err (F.slotOf i)
  /-- the supplied AP bound, one finite interval at a time, above the activation threshold -/
  bound : ∀ i ∈ F.slotIndex, F.activation ≤ i.1 →
    |discrepancy (F.slotOf i)| ≤ err (F.slotOf i)

/-! ## §D.3  The conditional `E_T` compiler -/

/-- The parity-family sign of a slot: family `0` (`q1 = 1`) enters with `+`, family `2`
(`q1 = 4`) with `−`, exactly as in the kernel-proved split `T = T⁰ − T²`. -/
def familySign (q1 : ℕ) : ℝ := if q1 = 1 then 1 else -1

theorem abs_familySign (q1 : ℕ) : |familySign q1| = 1 := by
  unfold familySign; split <;> norm_num

/-- The directed `E_T` aggregate: the supplied physical weight `w d` times the slot
discrepancy, summed once over each `(modulus, family, sign)` slot, with the family signs of
the `T⁰ − T²` split. -/
def E_T (F : PhysicalSlotFamily) (w : ℕ → ℝ) (A : PhysicalFixedResidueAPBound F) : ℝ :=
  ∑ i ∈ F.slotIndex, familySign i.2.1 * w i.1 * A.discrepancy (F.slotOf i)

/-- **`totLaneFixedResidueConditionalBound45`.**  `KERNEL-PROVED implication only`.

Given the external AP socket, the directed `E_T` aggregate obeys the symbolic bound

    |E_T| ≤ ∑_{(d,q1,s) ∈ D ×ˢ {1,4} ×ˢ {−1,+1}} |w d| · err(slot).

Each modulus contributes exactly four slots (`slotIndex_fiber_card`): two signs once, two
parity families once.  The Möbius cancellation is *not* used again here — it was consumed
once, exactly, by the source pairing of §B, which is why no absolute value appears before
this point.

The conclusion is symbolic in the supplied `err` and in the supplied weight `w`: no
numerical `E_T` bound, no `o(B_X)` claim, and no analytic theorem is asserted. -/
theorem totLaneFixedResidueConditionalBound45 (F : PhysicalSlotFamily) (w : ℕ → ℝ)
    (A : PhysicalFixedResidueAPBound F) :
    |E_T F w A| ≤ ∑ i ∈ F.slotIndex, |w i.1| * A.err (F.slotOf i) := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro i hi
  have hd : i.1 ∈ F.D := (Finset.mem_product.1 hi).1
  have hact : F.activation ≤ i.1 := F.D_activated _ hd
  have hb := A.bound i hi hact
  calc |familySign i.2.1 * w i.1 * A.discrepancy (F.slotOf i)|
      = |w i.1| * |A.discrepancy (F.slotOf i)| := by
        rw [abs_mul, abs_mul, abs_familySign, one_mul]
    _ ≤ |w i.1| * A.err (F.slotOf i) := by
        exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- **`totLaneFixedResidueConditionalBound45_factored`.**  `KERNEL-PROVED implication only`.
The same bound with the four slots of each modulus grouped: the physical weight norm times
the four supplied errors of that modulus. -/
theorem totLaneFixedResidueConditionalBound45_factored (F : PhysicalSlotFamily) (w : ℕ → ℝ)
    (A : PhysicalFixedResidueAPBound F) :
    |E_T F w A|
      ≤ ∑ d ∈ F.D, |w d| *
          ∑ j ∈ (({1, 4} : Finset ℕ) ×ˢ ({-1, 1} : Finset ℤ)), A.err (F.slotOf (d, j)) := by
  classical
  refine le_trans (totLaneFixedResidueConditionalBound45 F w A) (le_of_eq ?_)
  rw [PhysicalSlotFamily.slotIndex, Finset.sum_product]
  exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]

end September3ConditionalCompiler
end Erdos287
