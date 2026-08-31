import Mathlib
import RequestProject.Erdos287.QPacketPartition3221

/-!
# V24, §6–§7 — the full-`q` structural partition

`BALANCED7-QPACKET-STRUCTURAL-PARTITION45`

The Balanced7 comparison object is indexed by the factorisations `q · r = N`, `N = 2P + s`.
Fixing the cut `U = X^{1/3}`, every such factorisation lies in exactly one of the three
sectors

```
    SmallQ  :  q ≤ U
    SmallR  :  q > U  and  r ≤ U
    Hard    :  q > U  and  r > U
```

and inside the Hard sector the `q`-variable is cut dyadically by a partition of unity.

## What is proved here (all finite, all kernel-checked)

* `sectorOf` and `sum_threeWay_sector` — the exact three-way reassembly of any real-valued
  sum over `Nat.divisorsAntidiagonal N`;
* `balancedSeven_qr_threeWay_cover`, `balancedSeven_qr_threeWay_disjoint` — the three
  sectors cover the factorisation set and are pairwise disjoint;
* `hardDyadic_partitionOfUnity` — weighted reassembly of the Hard sector against any
  dyadic partition of unity;
* `dyadic_supports_not_disjoint` — a **firewall**: a smooth dyadic partition of unity may
  have overlapping supports, so the Hard sector is *not* a disjoint union of its dyadic
  cells.  Ownership must be assigned by the sharp owner map `qPacketOwner`, not by support;
* `balancedSeven_fullQ_structural_partition` — the combined statement.

## Provider ownership

`Provider` names the possible owners of a cell.  No cell is owned merely because a provider
name exists: `hardDyadicProvider_not_all_owned` exhibits a dyadic exponent whose owner is
`AnalyticOpen`, and both `SmallQProvider` and `SmallRProvider` are `SourceOpen`.
-/

namespace Erdos287
namespace V24FullQ

open Finset

/-! ## §6.1  The cut `U = X^{1/3}` -/

/-- The structural cut `U = X^{1/3}`. -/
noncomputable def uCut (X : ℝ) : ℝ := X ^ ((1 : ℝ) / 3)

theorem uCut_pos {X : ℝ} (hX : 0 < X) : 0 < uCut X := Real.rpow_pos_of_pos hX _

theorem uCut_cube {X : ℝ} (hX : 0 ≤ X) : uCut X ^ (3 : ℕ) = X := by
  rw [uCut, ← Real.rpow_natCast (X ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hX]
  norm_num

/-- The integer cut actually used to split the factorisation set. -/
noncomputable def uCutNat (X : ℝ) : ℕ := ⌊uCut X⌋₊

/-! ## §6.2  The three sectors -/

/-- The three structural sectors of a factorisation `q · r = N`. -/
inductive QSector
  | smallQ
  | smallR
  | hard
  deriving DecidableEq, Repr

/-- Sector of a factorisation pair `(q, r)` against the cut `u`. -/
def sectorOf (u : ℕ) (x : ℕ × ℕ) : QSector :=
  if x.1 ≤ u then QSector.smallQ else if x.2 ≤ u then QSector.smallR else QSector.hard

theorem sectorOf_smallQ {u : ℕ} {x : ℕ × ℕ} (h : x.1 ≤ u) :
    sectorOf u x = QSector.smallQ := by simp [sectorOf, h]

theorem sectorOf_smallR {u : ℕ} {x : ℕ × ℕ} (h1 : ¬ x.1 ≤ u) (h2 : x.2 ≤ u) :
    sectorOf u x = QSector.smallR := by simp [sectorOf, h1, h2]

theorem sectorOf_hard {u : ℕ} {x : ℕ × ℕ} (h1 : ¬ x.1 ≤ u) (h2 : ¬ x.2 ≤ u) :
    sectorOf u x = QSector.hard := by simp [sectorOf, h1, h2]

/-- The sector cells of the factorisation set of `N`. -/
def sectorCell (u N : ℕ) (S : QSector) : Finset (ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal N).filter (fun x => sectorOf u x = S)

theorem mem_sectorCell {u N : ℕ} {S : QSector} {x : ℕ × ℕ} :
    x ∈ sectorCell u N S ↔ x ∈ Nat.divisorsAntidiagonal N ∧ sectorOf u x = S := by
  simp [sectorCell]

/-! ## §6.3  Cover, disjointness, reassembly -/

/-- **`balancedSeven_qr_threeWay_cover`.**  The three sectors exhaust the factorisation set. -/
theorem balancedSeven_qr_threeWay_cover (u N : ℕ) :
    sectorCell u N QSector.smallQ ∪ sectorCell u N QSector.smallR
      ∪ sectorCell u N QSector.hard = Nat.divisorsAntidiagonal N := by
  ext x
  simp only [Finset.mem_union, mem_sectorCell]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro hx
    cases hs : sectorOf u x
    · exact Or.inl (Or.inl ⟨hx, rfl⟩)
    · exact Or.inl (Or.inr ⟨hx, rfl⟩)
    · exact Or.inr ⟨hx, rfl⟩

/-- **`balancedSeven_qr_threeWay_disjoint`.**  Distinct sectors are disjoint. -/
theorem balancedSeven_qr_threeWay_disjoint (u N : ℕ) {S T : QSector} (hST : S ≠ T) :
    Disjoint (sectorCell u N S) (sectorCell u N T) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  rw [mem_sectorCell] at hxS hxT
  exact hST (hxS.2 ▸ hxT.2 ▸ rfl)

/-- Three-way reassembly of an arbitrary real sum along a three-valued classifier. -/
theorem sum_threeWay (D : Finset (ℕ × ℕ)) (g : ℕ × ℕ → QSector) (f : ℕ × ℕ → ℝ) :
    ∑ x ∈ D, f x =
      (∑ x ∈ D.filter (fun x => g x = QSector.smallQ), f x)
        + (∑ x ∈ D.filter (fun x => g x = QSector.smallR), f x)
        + (∑ x ∈ D.filter (fun x => g x = QSector.hard), f x) := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  cases hgx : g x <;> simp

/-- **`sum_threeWay_sector`.**  The exact SmallQ / SmallR / Hard reassembly. -/
theorem sum_threeWay_sector (u N : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ x ∈ Nat.divisorsAntidiagonal N, f x =
      (∑ x ∈ sectorCell u N QSector.smallQ, f x)
        + (∑ x ∈ sectorCell u N QSector.smallR, f x)
        + (∑ x ∈ sectorCell u N QSector.hard, f x) :=
  sum_threeWay _ (sectorOf u) f

/-! ## §7  Dyadic partition of unity on the Hard sector -/

/-- A finite dyadic partition of unity with `K` cells on a finite index set `D`.

Supports are **not** required to be disjoint: this is exactly the smooth situation. -/
structure DyadicPartitionOfUnity (K : ℕ) (D : Finset (ℕ × ℕ)) where
  wt : ℕ → ℕ × ℕ → ℝ
  nonneg : ∀ k x, 0 ≤ wt k x
  normalized : ∀ x ∈ D, ∑ k ∈ Finset.range K, wt k x = 1

/-- **`hardDyadic_partitionOfUnity`.**  Weighted reassembly of a sum over the Hard sector. -/
theorem hardDyadic_partitionOfUnity {K : ℕ} {D : Finset (ℕ × ℕ)}
    (pu : DyadicPartitionOfUnity K D) (f : ℕ × ℕ → ℝ) :
    ∑ x ∈ D, f x = ∑ k ∈ Finset.range K, ∑ x ∈ D, pu.wt k x * f x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [← Finset.sum_mul, pu.normalized x hx, one_mul]

/-- An explicit two-cell partition of unity with completely overlapping supports. -/
noncomputable def overlapPartition : DyadicPartitionOfUnity 2 {((1 : ℕ), (1 : ℕ))} where
  wt := fun _ _ => 1 / 2
  nonneg := by intro _ _; norm_num
  normalized := by intro x _; norm_num

/-- **Firewall.**  A dyadic partition of unity need not have disjoint supports, so the Hard
sector is *not* presented as a disjoint union of its dyadic cells.  Ownership of a `q` must
be assigned by the sharp owner map `V23QPacket.qPacketOwner`. -/
theorem dyadic_supports_not_disjoint :
    ∃ x ∈ ({((1 : ℕ), (1 : ℕ))} : Finset (ℕ × ℕ)),
      overlapPartition.wt 0 x ≠ 0 ∧ overlapPartition.wt 1 x ≠ 0 := by
  refine ⟨(1, 1), by simp, ?_, ?_⟩ <;> · simp [overlapPartition]

/-- The sharp owner of a hard `q`-cell: the dyadic packet containing `q`. -/
def hardPacketOwner (q : ℕ) : ℕ := V23QPacket.qPacketOwner q

theorem hardPacketOwner_exists_unique {q : ℕ} (hq : 1 ≤ q) :
    ∃! k : ℕ, q ∈ V23QPacket.qPacket k :=
  V23QPacket.qPacket_exists_unique_owner hq

theorem hardPacketOwner_eq {k q : ℕ} (h : q ∈ V23QPacket.qPacket k) : k = hardPacketOwner q :=
  V23QPacket.qPacket_owner_unique h

/-! ## §7.2  The combined structural partition -/

/-- **`balancedSeven_fullQ_structural_partition`.**

Every real-valued sum over the factorisations of `N` decomposes exactly as

```
    SmallQ + SmallR + (dyadically weighted Hard cells).
```

This is a *reassembly* statement.  It says nothing about the size of any individual piece. -/
theorem balancedSeven_fullQ_structural_partition (u N K : ℕ) (f : ℕ × ℕ → ℝ)
    (pu : DyadicPartitionOfUnity K (sectorCell u N QSector.hard)) :
    ∑ x ∈ Nat.divisorsAntidiagonal N, f x =
      (∑ x ∈ sectorCell u N QSector.smallQ, f x)
        + (∑ x ∈ sectorCell u N QSector.smallR, f x)
        + ∑ k ∈ Finset.range K, ∑ x ∈ sectorCell u N QSector.hard, pu.wt k x * f x := by
  rw [sum_threeWay_sector u N f, hardDyadic_partitionOfUnity pu f]

/-! ## §7.3  Provider ownership -/

/-- The possible owners of a structural cell. -/
inductive Provider
  | Direct
  | Gate0TypeI
  | Gate1A
  | Gate1B
  | CurrentQ35
  | ExternalStandard
  | SourceOpen
  | AnalyticOpen
  deriving DecidableEq, Repr

/-- The SmallQ sector has no provider yet. -/
def SmallQProvider : Provider := Provider.SourceOpen

/-- The SmallR sector has no provider yet. -/
def SmallRProvider : Provider := Provider.SourceOpen

/-- The one hard dyadic exponent currently carrying a research closure candidate. -/
def q35Exponent : ℚ := 3 / 5

/-- Owner of the hard dyadic cell `Q = X^e`. -/
def HardDyadicProvider (e : ℚ) : Provider :=
  if e = q35Exponent then Provider.CurrentQ35 else Provider.AnalyticOpen

theorem hardDyadicProvider_q35 : HardDyadicProvider q35Exponent = Provider.CurrentQ35 := by
  simp [HardDyadicProvider]

theorem hardDyadicProvider_open_of_ne {e : ℚ} (h : e ≠ q35Exponent) :
    HardDyadicProvider e = Provider.AnalyticOpen := by
  simp [HardDyadicProvider, h]

/-- **Firewall.**  Not every hard dyadic cell is owned: `Q = X^{1/2}` is `AnalyticOpen`. -/
theorem hardDyadicProvider_not_all_owned :
    ∃ e : ℚ, HardDyadicProvider e = Provider.AnalyticOpen := by
  refine ⟨1 / 2, hardDyadicProvider_open_of_ne ?_⟩
  norm_num [q35Exponent]

theorem smallQProvider_open : SmallQProvider = Provider.SourceOpen := rfl

theorem smallRProvider_open : SmallRProvider = Provider.SourceOpen := rfl

/-- **Firewall.**  The existence of a provider *name* is not ownership: the SmallQ and SmallR
sectors and all hard dyadic cells except `Q = X^{3/5}` are recorded open. -/
theorem fullQ_ownership_incomplete :
    SmallQProvider = Provider.SourceOpen ∧ SmallRProvider = Provider.SourceOpen ∧
      ∃ e : ℚ, HardDyadicProvider e = Provider.AnalyticOpen :=
  ⟨rfl, rfl, hardDyadicProvider_not_all_owned⟩

end V24FullQ
end Erdos287
