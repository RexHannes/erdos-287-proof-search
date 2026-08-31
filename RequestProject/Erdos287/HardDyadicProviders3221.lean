import Mathlib
import RequestProject.Erdos287.FullQStructuralPartition3221
import RequestProject.Erdos287.PhysicalLogPrefactorRepair3221

/-!
# V24, §8 and §11 — the hard dyadic cells and their providers

`BALANCED7-HARD-DYADIC-CENSUS45`

The Hard sector `q > X^{1/3}`, `r > X^{1/3}` is cut into dyadic cells `Q ≈ X^e` with
`1/3 < e < 2/3`.  Exactly **one** of these cells, `e = 3/5`, carries a research closure
candidate (the repaired `C_ext = 1` prefactor of `PhysicalLogPrefactorRepair3221`, net log
exponent `−5/2`, signed margin `3`).  Every other cell is recorded `PROVIDER_OPEN`.

## Banked here

* `q35Cell` metadata with the *provable* consistency check `q35_Q_mul_R_eq_X`
  (`X^{3/5} · X^{2/5} = X`) and `q35_smoothCut_lt_Q`;
* `HardDyadicBalancedSevenPacket` — the per-cell packet record, with `hardExponentAdmissible`;
* `hardDyadic_owner_only_q35` — the census: the owner map returns `CurrentQ35` for `e = 3/5`
  and `AnalyticOpen` for every other admissible exponent;
* `HardDyadicProviderExhaustiveness287Input` — **uninhabited** interface asserting that all
  admissible dyadic cells are owned, together with `hardDyadicExhaustiveness_not_automatic`;
* §11 sign bookkeeping for the hard cell: one sign gives `2B(P)`, both signs `4B(P)`, and
  one sign alone does **not** give `4B(P)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V24Hard

open Erdos287.V24FullQ

/-! ## §8.1  The `Q = X^{3/5}` cell metadata -/

/-- Dyadic length of the current hard cell. -/
noncomputable def q35Q (X : ℝ) : ℝ := X ^ ((3 : ℝ) / 5)

/-- Complementary length of the current hard cell. -/
noncomputable def q35R (X : ℝ) : ℝ := X ^ ((2 : ℝ) / 5)

/-- The smooth cut used inside the current hard cell. -/
noncomputable def q35Y (X : ℝ) : ℝ := X ^ ((1 : ℝ) / 7)

/-- The Balanced7 depth coefficient of the physical cell. -/
def q35Coefficient : ℚ := -20

/-- The repaired external-log constant of the current hard cell. -/
def q35Cext : ℚ := Erdos287.V24Prefactor.sp2CextRepaired

theorem q35Cext_eq_one : q35Cext = 1 := rfl

/-- **`q35_Q_mul_R_eq_X`.**  `LEAN_PROVED`.  The cell lengths multiply back to `X`. -/
theorem q35_Q_mul_R_eq_X {X : ℝ} (hX : 0 < X) : q35Q X * q35R X = X := by
  rw [q35Q, q35R, ← Real.rpow_add hX]
  norm_num

/-- **`q35_smoothCut_lt_Q`.**  `LEAN_PROVED`.  The smooth cut sits strictly below `Q`. -/
theorem q35_smoothCut_lt_Q {X : ℝ} (hX : 1 < X) : q35Y X < q35Q X := by
  rw [q35Y, q35Q]
  exact Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)

/-- **`q35_inside_hard_sector`.**  `LEAN_PROVED`.  `X^{1/3} < Q < X^{2/3}`, so the cell is a
genuine Hard-sector cell. -/
theorem q35_inside_hard_sector {X : ℝ} (hX : 1 < X) :
    uCut X < q35Q X ∧ q35Q X < X ^ ((2 : ℝ) / 3) := by
  constructor
  · exact Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
  · exact Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)

/-! ## §8.2  Admissible dyadic exponents and their packets -/

/-- The admissible hard dyadic exponents `1/3 < e < 2/3`. -/
def hardExponentAdmissible (e : ℚ) : Prop := 1 / 3 < e ∧ e < 2 / 3

theorem q35_admissible : hardExponentAdmissible q35Exponent := by
  constructor <;> norm_num [q35Exponent]

/-- The per-cell Balanced7 packet record for the dyadic cell `Q ≈ X^e`. -/
structure HardDyadicBalancedSevenPacket (e : ℚ) : Prop where
  /-- The exponent is a genuine Hard-sector exponent. -/
  admissible : hardExponentAdmissible e
  /-- The cell's owner as recorded by the census. -/
  owned : HardDyadicProvider e = Provider.CurrentQ35

/-- **`hardDyadic_owner_only_q35`.**  `LEAN_PROVED`.

The census: a packet record exists only for the exponent `3/5`. -/
theorem hardDyadic_owner_only_q35 {e : ℚ} (h : HardDyadicBalancedSevenPacket e) :
    e = q35Exponent := by
  by_contra hne
  have := h.owned
  rw [hardDyadicProvider_open_of_ne hne] at this
  exact Provider.noConfusion this

/-- The `3/5` cell does carry a packet record. -/
theorem q35_packet : HardDyadicBalancedSevenPacket q35Exponent :=
  ⟨q35_admissible, hardDyadicProvider_q35⟩

/-- **`hardDyadic_census_incomplete`.**  `LEAN_PROVED`.

There is an admissible dyadic exponent with no owner, e.g. `e = 1/2`. -/
theorem hardDyadic_census_incomplete :
    ∃ e : ℚ, hardExponentAdmissible e ∧ HardDyadicProvider e = Provider.AnalyticOpen := by
  refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, hardDyadicProvider_open_of_ne ?_⟩
  norm_num [q35Exponent]

/-! ## §8.3  The exhaustiveness interface -/

/-- **`HardDyadicProviderExhaustiveness287Input`** — `EXTERNAL / UNINHABITED`.

The assertion that every admissible hard dyadic cell has a provider.  It is *false* for the
current census (`hardDyadic_census_incomplete`), which is precisely why it is an interface
and not a theorem. -/
structure HardDyadicProviderExhaustiveness287Input : Prop where
  /-- Every admissible exponent is owned. -/
  all_owned : ∀ e : ℚ, hardExponentAdmissible e → HardDyadicProvider e ≠ Provider.AnalyticOpen
  /-- No cell is owned twice: ownership is a function of the exponent. -/
  single_ownership : ∀ e f : ℚ, e = f → HardDyadicProvider e = HardDyadicProvider f

/-- **`hardDyadicExhaustiveness_not_automatic`.**  `LEAN_PROVED`.

The exhaustiveness interface is *refuted* by the current census, hence uninhabited. -/
theorem hardDyadicExhaustiveness_not_automatic :
    ¬ HardDyadicProviderExhaustiveness287Input := by
  intro h
  obtain ⟨e, he, hopen⟩ := hardDyadic_census_incomplete
  exact h.all_owned e he hopen

/-! ## §11  Sign bookkeeping for the hard cell -/

/-- One-sign matching of the hard cell against `2B(P)`. -/
def HardOneSignMatch (val B : ℝ) : Prop := val = 2 * B

/-- **`hardCell_twoSign_total`.**  `LEAN_PROVED`.  Both sign packages give `4B(P)`. -/
theorem hardCell_twoSign_total {vplus vminus B : ℝ}
    (hp : HardOneSignMatch vplus B) (hm : HardOneSignMatch vminus B) :
    vplus + vminus = 4 * B := by
  rw [HardOneSignMatch] at hp hm
  rw [hp, hm]; ring

/-- **`hardCell_oneSign_insufficient`.**  `LEAN_PROVED`.  One sign package alone does not
produce `4B(P)` unless `B = 0`. -/
theorem hardCell_oneSign_insufficient {v B : ℝ} (h : HardOneSignMatch v B) (hB : B ≠ 0) :
    v ≠ 4 * B := by
  rw [HardOneSignMatch] at h
  rw [h]
  intro hc
  apply hB
  linarith

/-- **Firewall `q35_closure_is_not_balancedSeven`.**  `LEAN_PROVED`.

Closing the single cell `e = 3/5` leaves admissible cells unowned, so it does not close the
Hard sector, let alone Balanced7. -/
theorem q35_closure_is_not_balancedSeven :
    HardDyadicBalancedSevenPacket q35Exponent ∧ ¬ HardDyadicProviderExhaustiveness287Input :=
  ⟨q35_packet, hardDyadicExhaustiveness_not_automatic⟩

end V24Hard
end Erdos287
