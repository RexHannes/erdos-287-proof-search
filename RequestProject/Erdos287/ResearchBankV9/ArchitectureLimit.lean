import RequestProject.Erdos287.ResearchBankV9.Gates

/-!
# Erdős #287 — Research Bank V9 §3G: the graph-architecture upper limit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a single-contact architecture whose useful distances lie in `[d, D]` (`D = ρ d`), the graph on
any finite set of integers with edges `d ≤ |x − y| ≤ D` has fractional chromatic number at most
`(D + d)/d = ρ + 1`.  Kernel-proved via the periodic interval independent sets

  `I_s = {x : (x − s) mod (D + d) < d}`,  `s ∈ [0, D + d)`:

* `periodic_indep` — each `I_s` is independent;
* `periodic_cover` — each vertex lies in exactly `d` of the `D + d` sets;
* `architecture_upper_limit` — a fractional colouring of value exactly `(D + d)/d` exists.

The analytic/transcendental requirement `ρ < e` is separate (`Gates.localization_constant`
gives `106/39 < e`); the observation that the chosen gate `145/39 = 106/39 + 1` lies just below
`e + 1` (`Gates.gate_near_architecture_limit`) is **arithmetic metadata only**, not a closure
theorem.
-/

open scoped BigOperators

namespace Erdos287
namespace ResearchBankV9
namespace ArchitectureLimit

/-- Adjacency in the single-contact architecture graph: useful distance in `[d, D]`. -/
def Adj (d D x y : ℤ) : Prop := d ≤ |x - y| ∧ |x - y| ≤ D

/-- A fractional colouring of a finite vertex set for a given adjacency. -/
structure FracColouring (V : Finset ℤ) (Adj : ℤ → ℤ → Prop) where
  /-- The independent sets used. -/
  sets : List (Finset ℤ)
  /-- Their weights. -/
  w : Finset ℤ → ℚ
  /-- Independence. -/
  indep : ∀ I ∈ sets, ∀ x ∈ I, ∀ y ∈ I, ¬ Adj x y
  /-- Nonnegativity. -/
  nonneg : ∀ I ∈ sets, 0 ≤ w I
  /-- Covering. -/
  cover : ∀ v ∈ V, 1 ≤ (sets.map fun I => if v ∈ I then w I else 0).sum

/-- The value of a fractional colouring. -/
def FracColouring.value {V : Finset ℤ} {A : ℤ → ℤ → Prop} (c : FracColouring V A) : ℚ :=
  (c.sets.map c.w).sum

/-- The periodic interval set `I_s` restricted to `V`. -/
def periodicSet (V : Finset ℤ) (d D s : ℤ) : Finset ℤ :=
  V.filter fun x => (x - s) % (D + d) < d

/-- **Each periodic interval set is independent.** -/
theorem periodic_indep {V : Finset ℤ} {d D : ℤ} (hd : 0 < d) (hD : 0 ≤ D) (s : ℤ) :
    ∀ x ∈ periodicSet V d D s, ∀ y ∈ periodicSet V d D s, ¬ Adj d D x y := by
  intro x hx y hy hadj
  simp only [periodicSet, Finset.mem_filter] at hx hy
  set P := D + d with hP
  have hP0 : 0 < P := by omega
  have ex := Int.emod_add_mul_ediv (x - s) P
  have ey := Int.emod_add_mul_ediv (y - s) P
  have hx0 := Int.emod_nonneg (x - s) hP0.ne'
  have hy0 := Int.emod_nonneg (y - s) hP0.ne'
  set α := (x - s) % P
  set β := (y - s) % P
  set a := (x - s) / P
  set b := (y - s) / P
  have hxy : x - y = P * (a - b) + (α - β) := by linarith
  obtain ⟨h1, h2⟩ := hadj
  rcases lt_trichotomy a b with hab | hab | hab
  · have : a - b ≤ -1 := by omega
    have : P * (a - b) ≤ -P := by nlinarith
    rw [abs_le] at h2
    rw [hxy] at h2 h1
    have : |P * (a - b) + (α - β)| = -(P * (a - b) + (α - β)) := abs_of_neg (by linarith)
    rw [this] at h1
    linarith [h2.1]
  · rw [hxy, hab, sub_self, mul_zero, zero_add] at h1
    have : |α - β| < d := abs_lt.2 ⟨by linarith [hy.2], by linarith [hx.2]⟩
    linarith
  · have : 1 ≤ a - b := by omega
    have : P ≤ P * (a - b) := by nlinarith
    rw [hxy] at h2
    have : |P * (a - b) + (α - β)| = P * (a - b) + (α - β) := abs_of_pos (by linarith)
    rw [this] at h2
    linarith

/-- **Exact covering**: each vertex lies in exactly `d` of the `D + d` periodic sets. -/
theorem periodic_cover {V : Finset ℤ} {d D : ℤ} (hd : 0 < d) (hD : 0 ≤ D) {v : ℤ} (hv : v ∈ V) :
    (((Finset.Ico 0 (D + d)).filter fun s => v ∈ periodicSet V d D s).card : ℤ) = d := by
  have : ((Finset.Ico 0 (D + d)).filter fun s => v ∈ periodicSet V d D s) =
      (CircularGraph.V (D + d)).filter fun s => (v - s) % (D + d) < d := by
    ext s; simp [periodicSet, hv, CircularGraph.V]
  rw [this]
  exact CircularGraph.count_shift_lt (by omega) hd.le (by omega) v

/-- **The architecture upper limit `χ_f ≤ (D + d)/d = ρ + 1`**: an explicit fractional colouring
of value exactly `(D + d)/d` exists on every finite vertex set. -/
theorem architecture_upper_limit (V : Finset ℤ) {d D : ℤ} (hd : 0 < d) (hD : 0 ≤ D) :
    ∃ c : FracColouring V (Adj d D), c.value = ((D + d : ℤ) : ℚ) / d := by
  classical
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨{ sets := (Finset.Ico 0 (D + d)).toList.map (periodicSet V d D)
            w := fun _ => 1 / d
            indep := ?_, nonneg := ?_, cover := ?_ }, ?_⟩
  · intro I hI
    simp only [List.mem_map] at hI
    obtain ⟨s, -, rfl⟩ := hI
    exact periodic_indep hd hD s
  · intro I _; positivity
  · intro v hv
    rw [List.map_map, Finset.sum_map_toList]
    simp only [Function.comp_def]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := periodic_cover hd hD hv
    have hc' : (((Finset.Ico 0 (D + d)).filter fun s => v ∈ periodicSet V d D s).card : ℚ) = d := by
      exact_mod_cast hc
    rw [hc']; field_simp; rfl
  · simp only [FracColouring.value, List.map_map, Finset.sum_map_toList, Function.comp_def,
      Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.Ico 0 (D + d)).card : ℤ) = D + d := by
      simp only [Int.card_Ico, sub_zero]; exact Int.toNat_of_nonneg (by omega)
    have hc' : ((Finset.Ico 0 (D + d)).card : ℚ) = ((D + d : ℤ) : ℚ) := by exact_mod_cast hc
    rw [hc']; ring

/-- In the programme's normalization `ρ = D/d`, the limit is `ρ + 1`. -/
theorem limit_eq_rho_add_one {d D : ℤ} (hd : 0 < d) :
    ((D + d : ℤ) : ℚ) / d = (D : ℚ) / d + 1 := by
  have : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast; field_simp

/-- The chosen gate is exactly the architecture limit at `ρ = 106/39` (`D = 106`, `d = 39`);
its admissibility uses the separate transcendental fact `106/39 < e`. -/
theorem gate_is_limit_at_rho :
    ((106 + 39 : ℤ) : ℚ) / 39 = 145 / 39 ∧ (106 : ℝ) / 39 < Real.exp 1 :=
  ⟨by norm_num, Gates.localization_constant.1⟩

end ArchitectureLimit
end ResearchBankV9
end Erdos287
