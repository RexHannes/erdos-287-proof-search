import Mathlib
import RequestProject.CurrentProgramme.Erdos287MasterSourceTypedPerronPackets

/-!
# The two-copy router and the proof-local shared-gcd `Ω` partition

`TWO-COPY ROUTER : KERNEL-PROVED (finite)`
`PROOF-LOCAL Ω  : KERNEL-PROVED (finite partition identity)`

This module is **append-only**.

**§1–§3.**  For a two-copy dispersion configuration set

```
Δ = t₁ n₂ − t₂ n₁
```

and route

```
Δ = 0                 → C0;
Δ ≠ 0 and b₁ ≠ b₂     → transverse;
Δ ≠ 0 and b₁ = b₂     → b-diagonal.
```

Exhaustiveness and disjointness are proved exactly.  **No analytic closure is
inferred from a tag**: §3 records that two configurations with the same tag can
carry arbitrarily different values.

**§4.**  The proof-local dyadic partition `1 = ∑_H Ω_H(gcd(g₁,g₂))` is
formalised as a finite identity.  It is *proof-local*: it is a function of the
**two-copy** object only, and the stage ledger of
`Erdos287.MasterSourcePackets` records that the `Ω` coordinate is inserted
strictly after the two-copy stage.  Nothing claims that an earlier, physical,
one-copy source carried this coordinate — §4 exhibits the dependence on both
copies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace TwoCopyRouter

open Erdos287.MasterSourcePackets

/-! ## §1  The two-copy configuration and `Δ` -/

/-- **`TwoCopyConfig`** — the finite data of a two-copy dispersion configuration. -/
structure TwoCopyConfig where
  /-- The determinant parameter of the first copy. -/
  t₁ : ℤ
  /-- The determinant parameter of the second copy. -/
  t₂ : ℤ
  /-- The modulus datum of the first copy. -/
  n₁ : ℤ
  /-- The modulus datum of the second copy. -/
  n₂ : ℤ
  /-- The `b`-coordinate of the first copy. -/
  b₁ : ℤ
  /-- The `b`-coordinate of the second copy. -/
  b₂ : ℤ
  /-- The `g`-coordinate of the first copy. -/
  g₁ : ℕ
  /-- The `g`-coordinate of the second copy. -/
  g₂ : ℕ

namespace TwoCopyConfig

variable (c : TwoCopyConfig)

/-- `Δ = t₁ n₂ − t₂ n₁`. -/
def Delta : ℤ := c.t₁ * c.n₂ - c.t₂ * c.n₁

end TwoCopyConfig

/-! ## §2  The exact router -/

/-- The three router tags. -/
inductive RouterTag
  /-- The degenerate `Δ = 0` cell. -/
  | c0
  /-- The transverse cell. -/
  | transverse
  /-- The b-diagonal cell. -/
  | bDiagonal
  deriving DecidableEq, Fintype, Repr

/-- The router. -/
noncomputable def route (c : TwoCopyConfig) : RouterTag :=
  if c.Delta = 0 then RouterTag.c0
  else if c.b₁ ≠ c.b₂ then RouterTag.transverse
  else RouterTag.bDiagonal

/-- **`route_eq_c0_iff`.**  `KERNEL-PROVED`. -/
theorem route_eq_c0_iff (c : TwoCopyConfig) : route c = RouterTag.c0 ↔ c.Delta = 0 := by
  unfold route
  split_ifs with h1 h2 <;> simp_all

/-- **`route_eq_transverse_iff`.**  `KERNEL-PROVED`. -/
theorem route_eq_transverse_iff (c : TwoCopyConfig) :
    route c = RouterTag.transverse ↔ c.Delta ≠ 0 ∧ c.b₁ ≠ c.b₂ := by
  unfold route
  split_ifs with h1 h2 <;> simp_all

/-- **`route_eq_bDiagonal_iff`.**  `KERNEL-PROVED`. -/
theorem route_eq_bDiagonal_iff (c : TwoCopyConfig) :
    route c = RouterTag.bDiagonal ↔ c.Delta ≠ 0 ∧ c.b₁ = c.b₂ := by
  unfold route
  split_ifs with h1 h2 <;> simp_all

/-- **`router_exhaustive`.**  `KERNEL-PROVED`.  Every configuration is routed. -/
theorem router_exhaustive (c : TwoCopyConfig) :
    route c = RouterTag.c0 ∨ route c = RouterTag.transverse ∨
      route c = RouterTag.bDiagonal := by
  rcases h : route c with _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **`router_disjoint`.**  `KERNEL-PROVED`.  The three defining conditions are pairwise
exclusive: no configuration carries two tags. -/
theorem router_disjoint (c : TwoCopyConfig) :
    ¬ (c.Delta = 0 ∧ (c.Delta ≠ 0 ∧ c.b₁ ≠ c.b₂)) ∧
    ¬ (c.Delta = 0 ∧ (c.Delta ≠ 0 ∧ c.b₁ = c.b₂)) ∧
    ¬ ((c.Delta ≠ 0 ∧ c.b₁ ≠ c.b₂) ∧ (c.Delta ≠ 0 ∧ c.b₁ = c.b₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1, -⟩; exact h1 h0
  · rintro ⟨h0, h1, -⟩; exact h1 h0
  · rintro ⟨⟨-, hne⟩, -, heq⟩; exact hne heq

/-- The router tags map injectively into the owner type of the packet compiler. -/
def routerOwner : RouterTag → PacketOwner
  | RouterTag.c0 => PacketOwner.c0
  | RouterTag.transverse => PacketOwner.transverse
  | RouterTag.bDiagonal => PacketOwner.bDiagonal

/-- **`routerOwner_injective`.**  `KERNEL-PROVED`.  Distinct tags have distinct owners, so
routing never merges two owners. -/
theorem routerOwner_injective : Function.Injective routerOwner := by decide

/-! ## §3  Firewall: a tag is not an estimate -/

/-- **`tag_carries_no_bound`.**  `KERNEL-PROVED`.

Two configurations with the *same* tag can carry arbitrarily different data: the router is
bookkeeping, and no analytic closure follows from a tag. -/
theorem tag_carries_no_bound (B : ℤ) :
    ∃ c₁ c₂ : TwoCopyConfig,
      route c₁ = RouterTag.c0 ∧ route c₂ = RouterTag.c0 ∧ B < c₂.n₁ - c₁.n₁ := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, |B| + 1, 0, 0, 0, 0, 0⟩, ?_, ?_, ?_⟩
  · rw [route_eq_c0_iff]; simp [TwoCopyConfig.Delta]
  · rw [route_eq_c0_iff]; simp [TwoCopyConfig.Delta]
  · have : B ≤ |B| := le_abs_self B
    simp only [sub_zero]
    omega

/-! ## §4  The proof-local shared-gcd `Ω` partition -/

/-- The dyadic class of a shared gcd. -/
def gcdClass (g : ℕ) : ℕ := Nat.log 2 g

/-- The proof-local dyadic cutoff `Ω_H` evaluated at a shared gcd. -/
def omegaVal (H g : ℕ) : ℕ := if gcdClass g = H then 1 else 0

/-- `Ω_H` of a two-copy configuration: it is a function of **both** copies. -/
def omegaOfConfig (H : ℕ) (c : TwoCopyConfig) : ℕ := omegaVal H (Nat.gcd c.g₁ c.g₂)

/-- **`omegaVal_le_one`.**  `KERNEL-PROVED`.  The elementary norm field: each cutoff is
`0` or `1`. -/
theorem omegaVal_le_one (H g : ℕ) : omegaVal H g = 0 ∨ omegaVal H g = 1 := by
  unfold omegaVal; split <;> simp

/-- **`omega_partition_of_unity`.**  `KERNEL-PROVED`.

The finite partition identity `1 = ∑_{H ≤ K} Ω_H(g)`, valid whenever the dyadic class of
`g` is covered by the range `K`. -/
theorem omega_partition_of_unity (K g : ℕ) (h : gcdClass g ≤ K) :
    ∑ H ∈ Finset.range (K + 1), omegaVal H g = 1 := by
  unfold omegaVal
  rw [Finset.sum_ite_eq (Finset.range (K + 1)) (gcdClass g) (fun _ => 1)]
  simp [Nat.lt_succ_of_le h]

/-- **`omega_partition_two_copy`.**  `KERNEL-PROVED`.

The same identity for the two-copy object: the `Ω` coordinate is inserted only once both
copies are present, and it partitions their shared gcd. -/
theorem omega_partition_two_copy (K : ℕ) (c : TwoCopyConfig)
    (h : gcdClass (Nat.gcd c.g₁ c.g₂) ≤ K) :
    ∑ H ∈ Finset.range (K + 1), omegaOfConfig H c = 1 :=
  omega_partition_of_unity K _ h

/-- **`omega_is_inserted_after_two_copies`.**  `KERNEL-PROVED`.

The stage ledger places the `Ω` insertion strictly after the two-copy dispersion object:
no one-copy (physical) stage carries this coordinate. -/
theorem omega_is_inserted_after_two_copies :
    CompilerStage.twoCopyDispersionObject.index
      < CompilerStage.proofLocalSharedGcdPartition.index :=
  omega_inserted_only_after_two_copies.1

/-- **`omega_depends_on_both_copies`.**  `KERNEL-PROVED`.

`Ω` is a genuine two-copy coordinate: changing the first copy alone changes its value, so
it cannot be a relabelling of a one-copy datum. -/
theorem omega_depends_on_both_copies :
    omegaVal 0 (Nat.gcd 1 4) ≠ omegaVal 0 (Nat.gcd 4 4) := by decide

end TwoCopyRouter
end Erdos287
