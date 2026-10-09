import RequestProject.Erdos287.ResearchBankV8.Saturation

/-!
# Erdős #287 — Research Bank V8 §2H: the target-scale rigid K2 obstruction (logical core)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

A complete owner row for a prime `p` (in the rigid regime `r_p = 0`, `d_p = p`) is a finite
cofactor set `C` with positive weights `h(c)` (in the programme `h(c) = J_p / c`); an assignment
`x` is row-valid iff `p ∣ ∑_{c ∈ C, x(pc) = 1} h(c)`.  The row is **rigid** (bounded height) when
`∑_{c∈C} h(c) < p`; its capacity is `κ = ⌊height / p⌋`, so rigid ⟺ `κ = 0`.

Kernel-proved:

* `rigid_row_forces_zero` — a rigid row forces every coordinate `pc`, `c ∈ C`, to be zero;
* `k2_forces_adjacent_zeros`, `k2_unsat` — with primes `p, q`, cofactors `α ∈ C_p`, `β ∈ C_q`,
  `α p − β q = 1`, the two complete rigid rows force the adjacent zeros `βq, βq+1`; with no-`00`
  the subsystem is UNSAT;
* `row_alone_compatible` — each row alone is path-compatible (no-`00` holds);
* `contact_unique` — under `pq > 2M` the physical contact `|αp − βq| = 1` with `αp, βq ≤ M` is
  unique;
* `rigid_row_avoids_selected_endpoint` — endpoint firewall: a rigid row cannot contain a selected
  endpoint.

The infinite prime supply of such `(p, q, α, β)` is the uninhabited interface `K2PrimeSupply`;
`k2_unsat_infinitely_often_of_supply` is conditional on it.

**Firewall** (`k2_does_not_refute_positive_capacity`): the rigid `κ = 0` obstruction does *not*
refute any statement about rows of capacity `κ ≥ 1` (e.g. the existing preprocessed
pseudoforest/orientation theorem); the raw K2 family is not claimed to defeat the preprocessed
positive-capacity kernel.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV8
namespace RigidK2

open Saturation

/-- A complete owner row in the rigid regime. -/
structure Row where
  /-- The owner prime (row modulus `d_p = p`). -/
  p : ℕ
  /-- The complete cofactor set. -/
  C : Finset ℕ
  /-- The row weights (`J_p / c` in the programme). -/
  h : ℕ → ℕ

/-- Row validity of an assignment. -/
def RowValid (R : Row) (x : ℕ → Bool) : Prop :=
  R.p ∣ ∑ c ∈ R.C.filter (fun c => x (R.p * c) = true), R.h c

/-- The row height `∑_{c ∈ C} h(c)`. -/
def height (R : Row) : ℕ := ∑ c ∈ R.C, R.h c

/-- The row capacity `κ = ⌊height / p⌋`. -/
def capacity (R : Row) : ℕ := height R / R.p

/-- Rigidity (bounded height with positive weights). -/
def Rigid (R : Row) : Prop := height R < R.p ∧ ∀ c ∈ R.C, 0 < R.h c

theorem rigid_iff_capacity_zero {R : Row} (hp : 0 < R.p) (hpos : ∀ c ∈ R.C, 0 < R.h c) :
    Rigid R ↔ capacity R = 0 := by
  unfold Rigid capacity
  rw [Nat.div_eq_zero_iff_lt hp]
  exact ⟨fun h => h.1, fun h => ⟨h, hpos⟩⟩

/-- **A rigid row forces all of its coordinates to be zero.** -/
theorem rigid_row_forces_zero {R : Row} (hR : Rigid R) {x : ℕ → Bool} (hx : RowValid R x) :
    ∀ c ∈ R.C, x (R.p * c) = false := by
  intro c hc
  by_contra hxc
  simp only [Bool.not_eq_false] at hxc
  have hle : ∑ c ∈ R.C.filter (fun c => x (R.p * c) = true), R.h c ≤ height R :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h0 := Nat.eq_zero_of_dvd_of_lt hx (lt_of_le_of_lt hle hR.1)
  rw [Finset.sum_eq_zero_iff] at h0
  have := h0 c (Finset.mem_filter.2 ⟨hc, hxc⟩)
  exact absurd this (hR.2 c hc).ne'

/-- **K2: two rigid complete rows with contact `αp = βq + 1` force adjacent zeros.** -/
theorem k2_forces_adjacent_zeros {Rp Rq : Row} (hRp : Rigid Rp) (hRq : Rigid Rq) {α β : ℕ}
    (hα : α ∈ Rp.C) (hβ : β ∈ Rq.C) (hcontact : Rp.p * α = Rq.p * β + 1) {x : ℕ → Bool}
    (hxp : RowValid Rp x) (hxq : RowValid Rq x) :
    x (Rq.p * β) = false ∧ x (Rq.p * β + 1) = false :=
  ⟨rigid_row_forces_zero hRq hxq β hβ, hcontact ▸ rigid_row_forces_zero hRp hxp α hα⟩

/-- **K2 is UNSAT together with no-`00`** on any interval containing the contact. -/
theorem k2_unsat {Rp Rq : Row} (hRp : Rigid Rp) (hRq : Rigid Rq) {α β : ℕ}
    (hα : α ∈ Rp.C) (hβ : β ∈ Rq.C) (hcontact : Rp.p * α = Rq.p * β + 1) {I : Finset ℕ}
    (hI : Rq.p * β ∈ I) (hI1 : Rq.p * β + 1 ∈ I) {x : ℕ → Bool}
    (hxp : RowValid Rp x) (hxq : RowValid Rq x) (hno : NoAdjZero I x) : False := by
  obtain ⟨h1, h2⟩ := k2_forces_adjacent_zeros hRp hRq hα hβ hcontact hxp hxq
  rcases hno _ hI hI1 with h | h <;> simp_all

/-- The canonical assignment compatible with one row: zeros exactly on the row. -/
def rowOnly (R : Row) : ℕ → Bool := fun n => !(decide (R.p ∣ n ∧ n / R.p ∈ R.C))

/-- **Each row alone is path-compatible**: `rowOnly R` is row-valid and has no adjacent zeros
(for `p ≥ 2`). -/
theorem row_alone_compatible (R : Row) (hp : 2 ≤ R.p) (I : Finset ℕ) :
    RowValid R (rowOnly R) ∧ NoAdjZero I (rowOnly R) := by
  constructor
  · unfold RowValid
    rw [Finset.filter_false_of_mem]
    · simp
    · intro c hc
      simp [rowOnly, Nat.mul_div_cancel_left c (by omega : 0 < R.p), hc]
  · intro n _ _
    by_contra hcon
    push_neg at hcon
    simp only [rowOnly, ne_eq, Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at hcon
    have h1 : R.p ∣ 1 := (Nat.dvd_add_right hcon.1.1).1 hcon.2.1
    have := Nat.le_of_dvd one_pos h1
    omega

/-- **Uniqueness of the physical contact** under `pq > 2M`. -/
theorem contact_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {M : ℕ}
    (hpq : 2 * M < p * q) {α β α' β' : ℤ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hα0' : 0 ≤ α')
    (hβ0' : 0 ≤ β') (hαM : p * α ≤ M) (hαM' : p * α' ≤ M)
    (hc : p * α - q * β = 1 ∨ p * α - q * β = -1)
    (hc' : p * α' - q * β' = 1 ∨ p * α' - q * β' = -1) : α = α' ∧ β = β' := by
  have hcop : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne.symm)
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hpq' : (2 * M : ℤ) < p * q := by exact_mod_cast hpq
  -- same-sign case
  have same : p * (α - α') = q * (β - β') → α = α' ∧ β = β' := by
    intro h
    have hd : (q : ℤ) ∣ α - α' := hcop.dvd_of_dvd_mul_left ⟨β - β', by rw [← h]⟩
    obtain ⟨k, hk⟩ := hd
    have hk' : (p : ℤ) * k = β - β' := by
      have : (q : ℤ) * (p * k) = q * (β - β') := by rw [← h, hk]; ring
      exact mul_left_cancel₀ (by positivity) this
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · exfalso
      have : (p : ℤ) * α' - p * α = p * q * (-k) := by rw [show α = α' + q * k by linarith]; ring
      nlinarith
    · subst hk0; constructor <;> linarith
    · exfalso
      have : (p : ℤ) * α - p * α' = p * q * k := by rw [show α = α' + q * k by linarith]; ring
      nlinarith
  -- opposite-sign case
  have opp : p * (α + α') = q * (β + β') → False := by
    intro h
    have hd : (q : ℤ) ∣ α + α' := hcop.dvd_of_dvd_mul_left ⟨β + β', by rw [← h]⟩
    obtain ⟨k, hk⟩ := hd
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · nlinarith
    · subst hk0
      have ha : α = 0 := by linarith
      have ha' : α' = 0 := by linarith
      subst ha; subst ha'
      rcases hc with h1 | h1 <;> nlinarith
    · have : (p : ℤ) * (α + α') = p * q * k := by rw [hk]; ring
      nlinarith
  rcases hc with h1 | h1 <;> rcases hc' with h2 | h2
  · exact same (by linarith)
  · exact (opp (by linarith)).elim
  · exact (opp (by linarith)).elim
  · exact same (by linarith)

/-- **Endpoint firewall**: a rigid row cannot contain a selected endpoint. -/
theorem rigid_row_avoids_selected_endpoint {R : Row} (hR : Rigid R) {c : ℕ} (hc : c ∈ R.C)
    {x : ℕ → Bool} (hsel : x (R.p * c) = true) : ¬ RowValid R x := by
  intro hx
  have := rigid_row_forces_zero hR hx c hc
  rw [hsel] at this
  exact absurd this (by decide)

/-! ## External prime supply (uninhabited) and the conditional consequence -/

/-- **External prime-supply interface — never inhabited here.**  Arbitrarily large scales `M`
carry primes `p, q` with rigid complete rows and a contact `αp = βq + 1 ≤ M`. -/
def K2PrimeSupply : Prop :=
  ∀ M₀ : ℕ, ∃ M ≥ M₀, ∃ (Rp Rq : Row) (α β : ℕ), Rp.p.Prime ∧ Rq.p.Prime ∧ Rigid Rp ∧
    Rigid Rq ∧ α ∈ Rp.C ∧ β ∈ Rq.C ∧ Rp.p * α = Rq.p * β + 1 ∧ 1 ≤ Rq.p * β ∧ Rp.p * α ≤ M

/-- **Conditional**: given the supply interface, arbitrarily large scales carry an UNSAT
two-row subsystem. -/
theorem k2_unsat_infinitely_often_of_supply (hsupply : K2PrimeSupply) :
    ∀ M₀ : ℕ, ∃ M ≥ M₀, ∃ Rp Rq : Row, ∀ x : ℕ → Bool,
      RowValid Rp x → RowValid Rq x → NoAdjZero (Finset.Icc 1 M) x → False := by
  intro M₀
  obtain ⟨M, hM, Rp, Rq, α, β, -, -, hRp, hRq, hα, hβ, hc, h1, hM'⟩ := hsupply M₀
  refine ⟨M, hM, Rp, Rq, fun x hxp hxq hno => ?_⟩
  exact k2_unsat hRp hRq hα hβ hc (Finset.mem_Icc.2 ⟨h1, by omega⟩)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hxp hxq hno

/-! ## Firewall: `κ = 0` obstructions do not refute `κ ≥ 1` theorems -/

/-- A statement quantified over rows of capacity `κ ≥ 1` (the shape of the preprocessed
positive-capacity pseudoforest/orientation theorem). -/
def PositiveCapacityStatement (Φ : Row → Prop) : Prop := ∀ R : Row, 1 ≤ capacity R → Φ R

/-- A concrete rigid K2 instance: `p = 3`, `q = 2`, `α = β = 1`, `3·1 − 2·1 = 1`. -/
def k2p : Row := ⟨3, {1}, fun _ => 1⟩
/-- The second row of the concrete K2 instance. -/
def k2q : Row := ⟨2, {1}, fun _ => 1⟩

theorem k2_instance : Rigid k2p ∧ Rigid k2q ∧ k2p.p * 1 = k2q.p * 1 + 1 ∧
    capacity k2p = 0 ∧ capacity k2q = 0 := by
  refine ⟨⟨by decide, by simp [k2p]⟩, ⟨by decide, by simp [k2q]⟩, rfl, by decide, by decide⟩

/-- Rigid rows lie outside the `κ ≥ 1` regime. -/
theorem rigid_not_positive_capacity {R : Row} (hR : Rigid R) : ¬ 1 ≤ capacity R := by
  unfold capacity
  rw [Nat.div_eq_of_lt hR.1]; omega

/-- **Firewall.**  The existence of rigid K2 obstructions does not refute positive-capacity
statements: there is a true positive-capacity statement coexisting with a rigid K2 instance. -/
theorem k2_does_not_refute_positive_capacity :
    ¬ ∀ Φ : Row → Prop, (Rigid k2p ∧ Rigid k2q ∧ k2p.p * 1 = k2q.p * 1 + 1) →
      ¬ PositiveCapacityStatement Φ := by
  intro h
  obtain ⟨h1, h2, h3, -, -⟩ := k2_instance
  exact h (fun _ => True) ⟨h1, h2, h3⟩ (fun _ _ => trivial)

end RigidK2
end ResearchBankV8
end Erdos287
