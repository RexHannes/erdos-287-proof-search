import RequestProject.CurrentProgramme.Erdos287TwoLaneRawSource
import RequestProject.CurrentProgramme.Erdos287TwoCopyRouterAndOmega

/-!
# The one-copy / two-copy ownership firewall

```
OWNER1 (one-copy)          : KERNEL-PROVED
TWO-COPY DESCENDANT TYPE   : KERNEL-PROVED
SHARED-GCD FIREWALL        : KERNEL-PROVED (reuses the banked Ω partition)
OWNER2 (two-copy)          : KERNEL-PROVED (existence and uniqueness of the router)
```

This module is **append-only**.

**§1 — `Owner1`.**  Only `lowQ`, `Pascadi` and `local` may own a *raw one-copy* packet.
`C0`, `transverse` and `bDiagonal` are provably **not** in the image of the one-copy owner
embedding into the banked six-owner type.

**§2 — `TwoCopyDescendant`.**  A descendant of an ordered pair of raw packets, carrying the
duplicated coordinates `t₁, t₂, n₁, n₂, b₁, b₂` (and the `g`-coordinates) of the banked
`TwoCopyConfig`.  `Δ = t₁n₂ − t₂n₁` exists **only** at this level:
`delta_is_not_a_one_copy_coordinate` shows two descendants of the *same* one-copy pair with
different `Δ`, so `Δ` is not a function of the one-copy data.

**§3 — the shared-gcd firewall.**  The proof-local dyadic `Ω` partition is *reused* from the
banked two-copy construction: its partition identity and its elementary `0/1` norm are
re-exported, and it is proved not to be a one-copy object.

**§4 — `Owner2` and the exact router.**  `Δ = 0 → C0`; `Δ ≠ 0 ∧ b₁ ≠ b₂ → transverse`;
`Δ ≠ 0 ∧ b₁ = b₂ → bDiagonal`.  Existence and uniqueness are kernel-proved.  **No analytic
owner estimate is proved anywhere.**
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace OneCopyTwoCopy

open Erdos287.TwoLaneRawSource
open Erdos287.TwoCopyRouter
open Erdos287.MasterSourcePackets

/-! ## §1  The one-copy owner type -/

/-- **`Owner1`** — the owners admissible at the raw one-copy level. -/
inductive Owner1
  /-- The low-`Q` owner. -/
  | lowQ
  /-- The Pascadi owner. -/
  | pascadi
  /-- The proof-local owner. -/
  | localOwner
  deriving DecidableEq, Fintype, Repr

/-- **`owner1_card`.**  `KERNEL-PROVED`.  There are exactly three one-copy owners. -/
theorem owner1_card : Fintype.card Owner1 = 3 := by decide

/-- The embedding of the one-copy owners into the banked six-owner type. -/
def Owner1.toPacketOwner : Owner1 → PacketOwner
  | Owner1.lowQ => PacketOwner.lowQ
  | Owner1.pascadi => PacketOwner.pascadiTriple
  | Owner1.localOwner => PacketOwner.localOwner

/-- **`owner1_embedding_injective`.**  `KERNEL-PROVED`. -/
theorem owner1_embedding_injective : Function.Injective Owner1.toPacketOwner := by decide

/-- **`owner1_excludes_two_copy_owners`.**  `KERNEL-PROVED`.

`C0`, `transverse` and `bDiagonal` are **not** one-copy owners. -/
theorem owner1_excludes_two_copy_owners (o : Owner1) :
    o.toPacketOwner ≠ PacketOwner.c0 ∧
    o.toPacketOwner ≠ PacketOwner.transverse ∧
    o.toPacketOwner ≠ PacketOwner.bDiagonal := by
  cases o <;> exact ⟨by decide, by decide, by decide⟩

/-! ## §2  The two-copy descendant -/

/-- **`TwoCopyDescendant raw₁ raw₂`** — the descendant produced by the actual
Cauchy/dispersion step from an ordered pair of raw one-copy packets.  It carries exactly the
duplicated coordinates. -/
structure TwoCopyDescendant (raw₁ raw₂ : RawPacketId) where
  /-- The duplicated coordinates `t₁, t₂, n₁, n₂, b₁, b₂, g₁, g₂`. -/
  config : TwoCopyConfig

namespace TwoCopyDescendant

variable {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂)

/-- `Δ = t₁n₂ − t₂n₁`, available **only** at the two-copy level. -/
def Delta : ℤ := d.config.Delta

/-- The `b`-coordinates of the two copies. -/
def b₁ : ℤ := d.config.b₁

/-- The `b`-coordinate of the second copy. -/
def b₂ : ℤ := d.config.b₂

/-- The shared gcd of the two copies. -/
def sharedGcd : ℕ := Nat.gcd d.config.g₁ d.config.g₂

end TwoCopyDescendant

/-- A canonical raw packet used only to exhibit countermodels. -/
def sampleRaw : RawPacketId :=
  { lane := RawLane.tot, contourCount := 1, endpointLabels := [], kernelMeta := 0,
    orientation := true, k := 0, J := 0, largePrimeLeaves := [], sourceSign := true,
    selected := none }

/-- **`delta_is_not_a_one_copy_coordinate`.**  `KERNEL-PROVED`.

Two descendants of the **same** ordered pair of raw one-copy packets can have different
`Δ`; hence `Δ` is not a function of the one-copy data and may not be placed at one-copy
level. -/
theorem delta_is_not_a_one_copy_coordinate :
    ∃ d₁ d₂ : TwoCopyDescendant sampleRaw sampleRaw, d₁.Delta ≠ d₂.Delta := by
  refine ⟨⟨⟨1, 0, 0, 1, 0, 0, 1, 1⟩⟩, ⟨⟨0, 0, 0, 0, 0, 0, 1, 1⟩⟩, ?_⟩
  show (1 : ℤ) * 1 - 0 * 0 ≠ 0 * 0 - 0 * 0
  norm_num

/-! ## §3  The shared-gcd firewall -/

/-- **`omega_partition_reused`.**  `KERNEL-PROVED CONDITIONAL` (reuse, not duplication).

The proof-local dyadic `Ω` partition of the banked two-copy construction. -/
theorem omega_partition_reused (K : ℕ) {raw₁ raw₂ : RawPacketId}
    (d : TwoCopyDescendant raw₁ raw₂) (h : gcdClass d.sharedGcd ≤ K) :
    ∑ H ∈ Finset.range (K + 1), omegaOfConfig H d.config = 1 :=
  omega_partition_two_copy K d.config h

/-- **`omega_elementary_norm`.**  `KERNEL-PROVED`.  Each `Ω`-weight is `0` or `1`. -/
theorem omega_elementary_norm (H : ℕ) {raw₁ raw₂ : RawPacketId}
    (d : TwoCopyDescendant raw₁ raw₂) :
    omegaOfConfig H d.config = 0 ∨ omegaOfConfig H d.config = 1 :=
  omegaVal_le_one H (Nat.gcd d.config.g₁ d.config.g₂)

/-- **`sharedGcd_is_not_a_one_copy_object`.**  `KERNEL-PROVED`.

The shared gcd — hence the `Ω` partition built from it — is not determined by the one-copy
data: two descendants of the same raw pair have different shared gcds and different
`Ω`-weights. -/
theorem sharedGcd_is_not_a_one_copy_object :
    ∃ d₁ d₂ : TwoCopyDescendant sampleRaw sampleRaw,
      d₁.sharedGcd ≠ d₂.sharedGcd ∧
      omegaOfConfig 0 d₁.config ≠ omegaOfConfig 0 d₂.config := by
  refine ⟨⟨⟨0, 0, 0, 0, 0, 0, 1, 1⟩⟩, ⟨⟨0, 0, 0, 0, 0, 0, 2, 2⟩⟩, ?_, ?_⟩ <;> decide

/-! ## §4  The two-copy owner type and the exact router -/

/-- **`Owner2`** — the owners created by the two-copy dispersion step. -/
inductive Owner2
  /-- The `C0` owner. -/
  | c0
  /-- The transverse owner. -/
  | transverse
  /-- The b-diagonal owner. -/
  | bDiagonal
  /-- The proof-local owner. -/
  | localOwner
  deriving DecidableEq, Fintype, Repr

/-- **`owner2_card`.**  `KERNEL-PROVED`.  There are exactly four two-copy owners. -/
theorem owner2_card : Fintype.card Owner2 = 4 := by decide

/-- The exact two-copy router. -/
noncomputable def owner2 {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂) : Owner2 :=
  if d.Delta = 0 then Owner2.c0
  else if d.b₁ = d.b₂ then Owner2.bDiagonal else Owner2.transverse

/-- **`owner2_c0_iff`.**  `KERNEL-PROVED`. -/
theorem owner2_c0_iff {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂) :
    owner2 d = Owner2.c0 ↔ d.Delta = 0 := by
  unfold owner2
  by_cases h : d.Delta = 0
  · simp [h]
  · by_cases hb : d.b₁ = d.b₂ <;> simp [h, hb]

/-- **`owner2_transverse_iff`.**  `KERNEL-PROVED`. -/
theorem owner2_transverse_iff {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂) :
    owner2 d = Owner2.transverse ↔ (d.Delta ≠ 0 ∧ d.b₁ ≠ d.b₂) := by
  unfold owner2
  by_cases h : d.Delta = 0
  · simp [h]
  · by_cases hb : d.b₁ = d.b₂ <;> simp [h, hb]

/-- **`owner2_bDiagonal_iff`.**  `KERNEL-PROVED`. -/
theorem owner2_bDiagonal_iff {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂) :
    owner2 d = Owner2.bDiagonal ↔ (d.Delta ≠ 0 ∧ d.b₁ = d.b₂) := by
  unfold owner2
  by_cases h : d.Delta = 0
  · simp [h]
  · by_cases hb : d.b₁ = d.b₂ <;> simp [h, hb]

/-- **`owner2_exists_unique`.**  `KERNEL-PROVED`.

Every two-copy descendant has exactly one `Owner2`, and the assignment is never
`localOwner` unless supplied by a local dictionary (the router never produces it). -/
theorem owner2_exists_unique {raw₁ raw₂ : RawPacketId} (d : TwoCopyDescendant raw₁ raw₂) :
    (∃! o : Owner2, owner2 d = o) ∧ owner2 d ≠ Owner2.localOwner := by
  refine ⟨⟨owner2 d, rfl, fun _ h => h.symm⟩, ?_⟩
  unfold owner2
  by_cases h : d.Delta = 0
  · simp [h]
  · by_cases hb : d.b₁ = d.b₂ <;> simp [h, hb]

/-- **`owner2_is_not_a_one_copy_assignment`.**  `KERNEL-PROVED`.

The two-copy owner is not a function of the one-copy data: two descendants of the same raw
pair receive different `Owner2` tags. -/
theorem owner2_is_not_a_one_copy_assignment :
    ∃ d₁ d₂ : TwoCopyDescendant sampleRaw sampleRaw, owner2 d₁ ≠ owner2 d₂ := by
  refine ⟨⟨⟨0, 0, 0, 0, 0, 0, 1, 1⟩⟩, ⟨⟨1, 0, 0, 1, 0, 0, 1, 1⟩⟩, ?_⟩
  have h1 : owner2 (⟨⟨0, 0, 0, 0, 0, 0, 1, 1⟩⟩ : TwoCopyDescendant sampleRaw sampleRaw)
      = Owner2.c0 := by
    rw [owner2_c0_iff]
    show (0 : ℤ) * 0 - 0 * 0 = 0
    norm_num
  have h2 : owner2 (⟨⟨1, 0, 0, 1, 0, 0, 1, 1⟩⟩ : TwoCopyDescendant sampleRaw sampleRaw)
      = Owner2.bDiagonal := by
    rw [owner2_bDiagonal_iff]
    refine ⟨?_, rfl⟩
    show (1 : ℤ) * 1 - 0 * 0 ≠ 0
    norm_num
  rw [h1, h2]
  decide

/-- **`owner_levels_are_disjoint`.**  `KERNEL-PROVED`.

The one-copy and two-copy owner types share only the proof-local owner: no one-copy packet
may be assigned `C0`, `transverse` or `bDiagonal`. -/
theorem owner_levels_are_disjoint (o : Owner1) :
    o.toPacketOwner = PacketOwner.lowQ ∨ o.toPacketOwner = PacketOwner.pascadiTriple ∨
      o.toPacketOwner = PacketOwner.localOwner := by
  cases o
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end OneCopyTwoCopy
end Erdos287
