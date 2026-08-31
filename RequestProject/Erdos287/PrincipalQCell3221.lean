import Mathlib
import RequestProject.Erdos287.MuLogQCell3221
import RequestProject.Erdos287.SP2PhysicalComparison3221

/-!
# V23, §4 — the principal `q`-cell: physical and factorial routes, and the
noncircularity firewall

`BALANCED7-PRINCIPAL-QCELL45`

Two *separately defined* objects:

* `M_phys_principal` — the **physical** principal `q`-cell.  The `μ·log` mass of the cell is
  deposited on the single admissible residue class `a_s(q) = −s·2⁻¹` inside the unit sector,
  normalised by `φ(q)`.  Its definition uses only the affine routing data of
  `MuLogQCell3221`.
* `M_fac_principal` — the **factorial-route** principal `q`-cell, the bare principal
  coefficient `μ(q)·log(z/q)/φ(q)`.

`principal_qCell_eq_physical_qCell` proves they agree pointwise for odd `q`.  This is
purely the algebra of the principal projection: exactly one class of the unit sector is
selected, and it carries the whole normalised mass.

## Firewall (mandatory)

Per the independent audit verdict `OPUS NANC : CASE F — SOURCE-MISSING`, the item
"independent physical `2B(P)`" is **not** verified.  Accordingly:

* the pointwise principal-cell equality is **not** allowed to stand in for the full
  `2B(P)` comparison — `principal_qCell_eq_does_not_prove_full_twoB` makes this
  machine-checkable;
* the missing ingredient is isolated as the *uninhabited* interface
  `SP2PhysicalTwoBIndependent287Input`, which demands a physical `2B(P)` defined from the
  SP-2 source independently of the factorial `q`-cell.

Nothing here is analytic; no inhabitant of the interface is produced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace V23Principal

open Erdos287.Vaughan Erdos287.V23QCell Erdos287.V23Comparison

/-! ## §4.1  The unit sector -/

/-- The unit sector of `ZMod q`, as a `Finset`. -/
def unitSector (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q))

theorem mem_unitSector {q : ℕ} [NeZero q] {a : ZMod q} :
    a ∈ unitSector q ↔ IsUnit a := by
  constructor
  · intro h
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
    exact hu ▸ u.isUnit
  · intro h
    obtain ⟨u, hu⟩ := h
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩

/-! ## §4.2  The two principal `q`-cells -/

/-- **`M_phys_principal`** — the physical principal `q`-cell.

The `μ·log` mass is deposited on the single admissible class `a_s(q)` of the unit sector. -/
noncomputable def M_phys_principal (s : AffineSign) (q : ℕ) [NeZero q] (z : ℝ) : ℝ :=
  ∑ a ∈ unitSector q,
    (if a = aCoeff s q then (moebius q : ℝ) * Real.log (z / q) / (q.totient : ℝ) else 0)

/-- **`M_fac_principal`** — the factorial-route principal `q`-cell: the bare principal
coefficient `μ(q) log(z/q)/φ(q)`. -/
noncomputable def M_fac_principal (q : ℕ) (z : ℝ) : ℝ :=
  (moebius q : ℝ) * Real.log (z / q) / (q.totient : ℝ)

/-- **`principal_qCell_eq_physical_qCell`.**  `LEAN_PROVED`.

For odd `q` the two principal `q`-cells agree pointwise.  Purely the algebra of the
principal projection — no analytic input, and no claim about `2B(P)`. -/
theorem principal_qCell_eq_physical_qCell {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q)
    (s : AffineSign) (z : ℝ) :
    M_phys_principal s q z = M_fac_principal q z := by
  classical
  rw [M_phys_principal, M_fac_principal]
  rw [Finset.sum_ite_eq' (unitSector q) (aCoeff s q)
    (fun _ => (moebius q : ℝ) * Real.log (z / q) / (q.totient : ℝ))]
  rw [if_pos (mem_unitSector.mpr (aCoeff_isUnit hq s))]

/-- **`affine_qCell_unique_class`.**  `LEAN_PROVED`.

The physical principal cell is supported on exactly one residue class: for odd `q` there is
a *unique* `a` such that `q ∣ 2P + s` is equivalent to `P ≡ a`, namely `a = a_s(q)`. -/
theorem affine_qCell_unique_class {q : ℕ} [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) :
    ∃! a : ZMod q, ∀ P : ℤ, ((q : ℤ) ∣ 2 * P + s.val) ↔ (P : ZMod q) = a := by
  refine ⟨aCoeff s q, fun P => aCoeff_spec hq s P, ?_⟩
  intro b hb
  have hcast : (((ZMod.val (aCoeff s q) : ℕ) : ℤ) : ZMod q) = aCoeff s q := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hdvd : ((q : ℤ) ∣ 2 * ((ZMod.val (aCoeff s q) : ℕ) : ℤ) + s.val) :=
    (aCoeff_spec hq s _).mpr hcast
  have := (hb _).mp hdvd
  rw [hcast] at this
  exact this.symm

/-! ## §4.3  The missing independent physical `2B(P)` -/

/-- **`SP2PhysicalTwoBIndependent287Input`** — `EXTERNAL / SOURCE-MISSING / UNINHABITED`.

The independent audit records `independent physical 2B(P)` as *not verified*.  This
interface is the exact missing statement: the singular-series datum `B` carried by the
physical cell must be *independently defined from the SP-2 source*, i.e. it must coincide
with a function `Bsrc` produced by the source layer, with the aggregate `μ/φ` sum
converging to `2·Bsrc(P)` on the physical family, uniformly and with the *factorial*
`q`-cell playing no role in the definition of `Bsrc`.

No inhabitant is constructed anywhere in this repository. -/
structure SP2PhysicalTwoBIndependent287Input
    (C : SP2PhysicalCell) (Bsrc : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp : ℝ) : Prop where
  /-- The physical `B`-field of the cell is the SP-2 source function, not a re-labelling of
  the factorial `q`-cell. -/
  physical_B_is_source : ∀ pv ∈ C.cell, C.B (physModulus pv) = Bsrc (physModulus pv)
  /-- The source function is defined on the whole physical family. -/
  source_total : ∀ pv ∈ C.cell, 0 ≤ Bsrc (physModulus pv)
  /-- The aggregate `μ/φ log` sum converges to `2·Bsrc(P)` with a `log^{-A}` saving,
  uniformly over the physical seven-prime family. -/
  aggregate_limit : ∀ pv ∈ C.cell, ∀ z : ℝ, 2 ≤ z →
    |J (physModulus pv) z - 2 * Bsrc (physModulus pv)| ≤ (Real.log z) ^ (-Aexp)
  /-- The declared log saving is positive (a genuine saving). -/
  saving_positive : 0 < Aexp

/-- **`sp2PhysicalTwoBIndependent_not_automatic`.**  `LEAN_PROVED`.

The interface is a genuine restriction: explicit data refute it, so it cannot be discharged
by generalities. -/
theorem sp2PhysicalTwoBIndependent_not_automatic :
    ∃ (C : SP2PhysicalCell) (Bsrc : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (Aexp : ℝ),
      ¬ SP2PhysicalTwoBIndependent287Input C Bsrc J Aexp := by
  classical
  refine ⟨⟨{fun _ => 1}, fun _ => 1, fun _ => 0⟩, fun _ => -1, fun _ _ => 0, 1, ?_⟩
  intro h
  have h1 := h.source_total (fun _ => 1) (Finset.mem_singleton_self _)
  norm_num at h1

/-! ## §4.4  Noncircularity firewall -/

/-- **`principal_qCell_eq_does_not_prove_full_twoB`.**  `LEAN_PROVED`.

The mandated firewall.  `principal_qCell_eq_physical_qCell` holds *unconditionally* for
every odd `q`, whereas the full physical comparison `−20 ∑ Ω [Λ(2P+s) − 2B(P)]` can be
nonzero.  Hence the principal-cell identity cannot, by itself, prove the full physical
`2B(P)` statement: an implication from an unconditional truth to a refutable statement is
impossible. -/
theorem principal_qCell_eq_does_not_prove_full_twoB :
    ∃ (C : SP2PhysicalCell) (s : AffineSign),
      SP2BalancedSevenPhysicalComparison C s ≠ 0 :=
  sp2PhysicalComparison_not_automatically_zero

/-- **`principal_qCell_identity_is_unconditional`.**  `LEAN_PROVED`.

The companion half of the firewall: the principal-cell identity really is unconditional on
odd moduli, so it carries no `2B(P)` information whatsoever. -/
theorem principal_qCell_identity_is_unconditional
    (q : ℕ) [NeZero q] (hq : ¬ 2 ∣ q) (s : AffineSign) (z : ℝ) :
    M_phys_principal s q z = M_fac_principal q z :=
  principal_qCell_eq_physical_qCell hq s z

end V23Principal
end Erdos287
