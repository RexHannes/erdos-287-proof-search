import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V8 §2K: the virtual-edge firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Eliminating (projecting out) an interior coordinate of a full arithmetic row can produce a
Boolean relation between **physically nonadjacent** exterior coordinates — a *virtual edge*.

* `virtual_edge_from_row` — the row `x₁ + y + x₃ ≡ 0 (mod 3)` on positions `1, 2, 3`, projected
  onto `(x₁, x₃)`, is exactly the relation `x₁ = x₃`;
* `virtual_edge_not_physical_contact` — positions `1` and `3` do not satisfy the physical contact
  equation `|u − v| = 1`, so a virtual edge is **not** a new contact equation `Q_p c − Q_q d = ±1`;
* `virtual_edges_not_independent` — the three virtual edges of one row are *not* arithmetically
  independent: the naive product density `1/8` differs from the true density `2/8`; any
  certificate count must expand virtual constraints back to the originating row.
-/

namespace Erdos287
namespace ResearchBankV8
namespace VirtualEdge

/-- The full arithmetic row on three coordinates: `x₁ + y + x₃ ≡ 0 (mod 3)`. -/
def row (x₁ y x₃ : Bool) : Bool := (x₁.toNat + y.toNat + x₃.toNat) % 3 == 0

/-- The projection of the row onto the exterior coordinates. -/
def projected (x₁ x₃ : Bool) : Bool := row x₁ false x₃ || row x₁ true x₃

/-- **Virtual edge.**  The projection is exactly the equality relation `x₁ = x₃`. -/
theorem virtual_edge_from_row : ∀ x₁ x₃ : Bool, projected x₁ x₃ = (x₁ == x₃) := by decide

/-- The projected relation is a genuine (nontrivial) constraint. -/
theorem virtual_edge_nontrivial : projected true false = false ∧ projected true true = true := by
  decide

/-- Physical contact between two positions. -/
def PhysicalContact (u v : ℤ) : Prop := u - v = 1 ∨ u - v = -1

/-- **A virtual edge is not a physical contact.** -/
theorem virtual_edge_not_physical_contact : ¬ PhysicalContact 1 3 ∧ ¬ PhysicalContact 3 1 := by
  unfold PhysicalContact; omega

/-- Row on three coordinates: `a + b + c ≡ 0 (mod 3)`. -/
def row3 (a b c : Bool) : Bool := (a.toNat + b.toNat + c.toNat) % 3 == 0

/-- Number of satisfying assignments of the full row. -/
def rowCount : ℕ :=
  ((List.product [false, true] (List.product [false, true] [false, true])).filter
    fun t => row3 t.1 t.2.1 t.2.2).length

/-- **Virtual edges from one row are not independent.**  The row has `2` of `8` solutions (density
`1/4`); its three virtual edges `a = b`, `b = c`, `a = c` each have density `1/2`, whose naive
product is `1/8 ≠ 1/4`. -/
theorem virtual_edges_not_independent :
    rowCount = 2 ∧ ((1 : ℚ) / 2) ^ 3 ≠ (rowCount : ℚ) / 8 := by
  refine ⟨by decide, ?_⟩
  rw [show rowCount = 2 by decide]; norm_num

/-- The projections onto each pair coincide with the three equality edges. -/
theorem three_virtual_edges :
    (∀ a b : Bool, (row3 a b false || row3 a b true) = (a == b)) ∧
    (∀ b c : Bool, (row3 false b c || row3 true b c) = (b == c)) ∧
    (∀ a c : Bool, (row3 a false c || row3 a true c) = (a == c)) := by decide

end VirtualEdge
end ResearchBankV8
end Erdos287
