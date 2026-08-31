import Mathlib

/-!
# V23, §7 — the dyadic `q`-packet partition compiler

`BALANCED7-QPACKET-PARTITION45`

Finite ownership of `q`-cells.  Each modulus `q ≥ 1` is owned by exactly one dyadic packet

```
    packet k = [2^k, 2^{k+1}),      owner q = ⌊log₂ q⌋,
```

and the following are proved:

* `qPacket_owner_mem`      — every `q ≥ 1` lies in its own packet;
* `qPacket_owner_unique`   — a `q` lying in packet `k` forces `k = owner q` (no duplicate
  ownership);
* `qPacket_disjoint`       — distinct packets are disjoint;
* `qPacket_cover`          — the packets `k < K` cover exactly `[1, 2^K)`;
* `qPacket_reassembly`     — consequently the packet sums reassemble the full sum with no
  omission and no double counting.

## Firewall (mandatory)

The reassembly theorem above is about an *arbitrary* cell weight `M`.  It does **not** say
that the physical Balanced7 `q ~ Q` analytic cell is the principal `q`-cell of the source,
nor that the physical packets exhaust the source's own `q` range: the independent audit
(`OPUS NANC : CASE F — SOURCE-MISSING`) lists `dyadic-q / full-q exhaustiveness` as *not
verified*.  Those two statements are isolated as the uninhabited interfaces

* `BalancedSevenQPartitionInput`,
* `BalancedSevenQPacketExhaustiveness287Input`,

and full `2B(P)` reassembly is only available once *all* physical `q`-cells are summed —
`qPacket_reassembly_needs_all_packets` records that a proper sub-range does not suffice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V23QPacket

/-! ## §7.1  Packets and owners -/

/-- The dyadic packet `[2^k, 2^{k+1})`. -/
def qPacket (k : ℕ) : Finset ℕ := Finset.Ico (2 ^ k) (2 ^ (k + 1))

/-- **`qPacketOwner`** — the unique packet index owning the modulus `q`. -/
def qPacketOwner (q : ℕ) : ℕ := Nat.log 2 q

theorem mem_qPacket {k q : ℕ} : q ∈ qPacket k ↔ 2 ^ k ≤ q ∧ q < 2 ^ (k + 1) :=
  Finset.mem_Ico

/-- **`qPacket_owner_mem`.**  `LEAN_PROVED`.  Every `q ≥ 1` lies in the packet it owns. -/
theorem qPacket_owner_mem {q : ℕ} (hq : 1 ≤ q) : q ∈ qPacket (qPacketOwner q) := by
  rw [mem_qPacket]
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) q⟩

/-- **`qPacket_owner_unique`.**  `LEAN_PROVED`.  No duplicate ownership. -/
theorem qPacket_owner_unique {k q : ℕ} (h : q ∈ qPacket k) : k = qPacketOwner q := by
  rw [mem_qPacket] at h
  exact (Nat.log_eq_of_pow_le_of_lt_pow h.1 h.2).symm

/-- **`qPacket_disjoint`.**  `LEAN_PROVED`.  Distinct packets are disjoint. -/
theorem qPacket_disjoint {k l : ℕ} (hkl : k ≠ l) : Disjoint (qPacket k) (qPacket l) := by
  rw [Finset.disjoint_left]
  intro q hk hl
  exact hkl ((qPacket_owner_unique hk).trans (qPacket_owner_unique hl).symm)

/-- **`qPacket_exists_unique_owner`.**  `LEAN_PROVED`.

Exhaustiveness plus uniqueness in one statement: every `q ≥ 1` belongs to exactly one
packet. -/
theorem qPacket_exists_unique_owner {q : ℕ} (hq : 1 ≤ q) : ∃! k : ℕ, q ∈ qPacket k :=
  ⟨qPacketOwner q, qPacket_owner_mem hq, fun _ h => qPacket_owner_unique h⟩

/-- **`qPacket_cover`.**  `LEAN_PROVED`.

The packets with index `< K` cover exactly the moduli in `[1, 2^K)`. -/
theorem qPacket_cover (K : ℕ) :
    (Finset.range K).biUnion qPacket = Finset.Ico 1 (2 ^ K) := by
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_qPacket, Finset.mem_Ico]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    refine ⟨le_trans (Nat.one_le_two_pow) h1, lt_of_lt_of_le h2 ?_⟩
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rintro ⟨h1, h2⟩
    refine ⟨qPacketOwner q, ?_, (mem_qPacket.mp (qPacket_owner_mem h1)).1,
      (mem_qPacket.mp (qPacket_owner_mem h1)).2⟩
    exact Nat.log_lt_of_lt_pow (by omega) h2

/-! ## §7.2  Exact reassembly -/

/-- **`qPacket_reassembly`.**  `LEAN_PROVED`.

Summing an arbitrary cell weight over the packets `k < K` reproduces the sum over
`[1, 2^K)` exactly: no omission, no double counting. -/
theorem qPacket_reassembly (K : ℕ) (M : ℕ → ℝ) :
    ∑ k ∈ Finset.range K, ∑ q ∈ qPacket k, M q = ∑ q ∈ Finset.Ico 1 (2 ^ K), M q := by
  classical
  rw [← qPacket_cover K, Finset.sum_biUnion]
  intro k _ l _ hkl
  exact qPacket_disjoint hkl

/-- **`qPacket_reassembly_needs_all_packets`.**  `LEAN_PROVED`.

A single packet does not reassemble the full sum: taking `M = 1`, the packet `k = 0` gives
`1` while the range `[1, 4)` gives `3`.  This is the machine-checkable form of "full `2B(P)`
reassembly occurs only after *all* physical `q`-cells are summed". -/
theorem qPacket_reassembly_needs_all_packets :
    ∑ _q ∈ qPacket 0, (1 : ℝ) ≠ ∑ _q ∈ Finset.Ico 1 (2 ^ 2), (1 : ℝ) := by
  norm_num [qPacket]

/-! ## §7.3  The uninhabited source interfaces -/

/-- **`BalancedSevenQPartitionInput`** — `EXTERNAL / SOURCE-MISSING / UNINHABITED`.

The repository does not contain the full `q` partition of the physical Balanced7 source.
This interface states it: a packet index set, a declared owner for each source modulus, and
the requirement that the analytic cell currently treated (the `q ~ Q` cell) is exactly the
packet it claims. -/
structure BalancedSevenQPartitionInput
    (sourceModuli : Finset ℕ) (owner : ℕ → ℕ) (indexSet : Finset ℕ) (Qcell : ℕ) : Prop where
  /-- Every source modulus is owned by a declared packet index. -/
  owner_mem_index : ∀ q ∈ sourceModuli, owner q ∈ indexSet
  /-- The declared owner is the dyadic one. -/
  owner_is_dyadic : ∀ q ∈ sourceModuli, owner q = qPacketOwner q
  /-- Every declared packet index is actually used. -/
  index_used : ∀ k ∈ indexSet, ∃ q ∈ sourceModuli, owner q = k
  /-- The currently treated analytic cell is one of the declared packets. -/
  current_cell : Qcell ∈ indexSet

/-- **`BalancedSevenQPacketExhaustiveness287Input`** — `EXTERNAL / SOURCE-MISSING /
UNINHABITED`.

The audit item `dyadic-q / full-q exhaustiveness`.  Fields: the packet index set, the
membership predicate, the cover, pairwise disjointness with boundary ownership, the current
`q ~ Q` owner, the treatment of all other owners, and the resulting full Euler
reassembly. -/
structure BalancedSevenQPacketExhaustiveness287Input
    (sourceModuli : Finset ℕ) (indexSet : Finset ℕ) (owner : ℕ → ℕ) (Qcell : ℕ)
    (cellValue : ℕ → ℝ) (target : ℝ) : Prop where
  /-- Membership: a modulus belongs to the packet of its owner. -/
  membership : ∀ q ∈ sourceModuli, q ∈ qPacket (owner q)
  /-- Cover: the declared packets exhaust the source moduli. -/
  cover : ∀ q ∈ sourceModuli, owner q ∈ indexSet
  /-- Boundary ownership: the dyadic boundaries are assigned once and for all. -/
  boundary : ∀ q ∈ sourceModuli, ∀ k, q ∈ qPacket k → k = owner q
  /-- The current analytic cell is a declared packet. -/
  current_owner : Qcell ∈ indexSet
  /-- Every other packet is also accounted for. -/
  other_owners : ∀ k ∈ indexSet, k ≠ Qcell → ∃ q ∈ sourceModuli, owner q = k
  /-- Full reassembly: the packet sums add up to the analytic target. -/
  full_reassembly : ∑ k ∈ indexSet, ∑ q ∈ sourceModuli.filter (fun q => owner q = k),
    cellValue q = target

/-- **`qPartitionInput_not_automatic`.**  `LEAN_PROVED`. -/
theorem qPartitionInput_not_automatic :
    ∃ (sourceModuli : Finset ℕ) (owner : ℕ → ℕ) (indexSet : Finset ℕ) (Qcell : ℕ),
      ¬ BalancedSevenQPartitionInput sourceModuli owner indexSet Qcell := by
  refine ⟨∅, id, ∅, 0, ?_⟩
  intro h
  simpa using h.current_cell

/-- **`qPacketExhaustiveness_not_automatic`.**  `LEAN_PROVED`. -/
theorem qPacketExhaustiveness_not_automatic :
    ∃ (sourceModuli indexSet : Finset ℕ) (owner : ℕ → ℕ) (Qcell : ℕ)
      (cellValue : ℕ → ℝ) (target : ℝ),
      ¬ BalancedSevenQPacketExhaustiveness287Input sourceModuli indexSet owner Qcell
        cellValue target := by
  refine ⟨∅, ∅, id, 0, fun _ => 0, 1, ?_⟩
  intro h
  simpa using h.current_owner

end V23QPacket
end Erdos287
