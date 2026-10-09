import RequestProject.Erdos287.Direct.TargetTuningFinite

/-!
# Route D — the exact signed absorber interface

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For a finite family of signed rational increments `ξ_i` put

`D_buf = lcm_i den(ξ_i)`,  `b_buf = gcd_i (D_buf · ξ_i)`.

Kernel-proved here are the **necessary lattice conditions** for a residual `e` to be an exact
signed combination of the increments:

* `D_buf · e` is an integer (`bufDen_mul_mem_int`);
* `b_buf ∣ D_buf · e` (`absorber_lattice_necessary`).

The predicate `ExactSignedAbsorber`, expressing a bounded binary selection of *physically
compatible* protected switches realising the residual exactly, is defined and **deliberately
not inhabited**.  Its status is `OPEN`.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.35  Buffer denominator and buffer gcd -/

/-- The buffer denominator `D_buf = lcm_i den(ξ_i)`. -/
def bufDen {ι : Type*} (S : Finset ι) (xi : ι → ℚ) : ℕ := S.lcm (fun i => (xi i).den)

/-- The integer `D · r`, valid when `den r ∣ D`. -/
def carryNum (D : ℕ) (r : ℚ) : ℤ := ((D / r.den : ℕ) : ℤ) * r.num

/-- **`carryNum_spec`.**  `KERNEL-PROVED`.  `carryNum` really computes `D · r` whenever the
denominator divides `D`. -/
theorem carryNum_spec {D : ℕ} {r : ℚ} (h : r.den ∣ D) : ((carryNum D r : ℤ) : ℚ) = (D : ℚ) * r := by
  obtain ⟨k, rfl⟩ := h
  rw [carryNum, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero r.den_nz)]
  push_cast
  calc (k : ℚ) * (r.num : ℚ) = (k : ℚ) * ((r.den : ℚ) * r) := by rw [Rat.den_mul_eq_num]
    _ = (r.den : ℚ) * (k : ℚ) * r := by ring

theorem den_dvd_bufDen {ι : Type*} {S : Finset ι} {xi : ι → ℚ} {i : ι} (hi : i ∈ S) :
    (xi i).den ∣ bufDen S xi := Finset.dvd_lcm hi

/-- The buffer gcd `b_buf = gcd_i (D_buf · ξ_i)`. -/
def bufGcd {ι : Type*} (S : Finset ι) (xi : ι → ℚ) : ℤ :=
  S.gcd (fun i => carryNum (bufDen S xi) (xi i))

theorem bufGcd_dvd {ι : Type*} {S : Finset ι} {xi : ι → ℚ} {i : ι} (hi : i ∈ S) :
    bufGcd S xi ∣ carryNum (bufDen S xi) (xi i) := Finset.gcd_dvd hi

/-! ## D.36  The necessary lattice conditions -/

/-- **`bufDen_mul_mem_int`.**  `KERNEL-PROVED`.  If the residual `e` is a signed subfamily sum
of the increments, then `D_buf · e` is an integer, namely the corresponding sum of the
`carryNum`s. -/
theorem bufDen_mul_mem_int {ι : Type*} [DecidableEq ι] {S T : Finset ι} {xi : ι → ℚ} {e : ℚ}
    (hTS : T ⊆ S) (he : e = ∑ i ∈ T, xi i) :
    ((bufDen S xi : ℚ)) * e = ((∑ i ∈ T, carryNum (bufDen S xi) (xi i) : ℤ) : ℚ) := by
  rw [he, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [carryNum_spec (den_dvd_bufDen (hTS hi))]

/-- **`absorber_lattice_necessary`.**  `KERNEL-PROVED`.  The exact lattice condition: the
integer `D_buf · e` is divisible by `b_buf`. -/
theorem absorber_lattice_necessary {ι : Type*} [DecidableEq ι] {S T : Finset ι} {xi : ι → ℚ}
    {e : ℚ} (hTS : T ⊆ S) (he : e = ∑ i ∈ T, xi i) :
    ∃ m : ℤ, ((bufDen S xi : ℚ)) * e = (m : ℚ) ∧ bufGcd S xi ∣ m := by
  refine ⟨∑ i ∈ T, carryNum (bufDen S xi) (xi i), bufDen_mul_mem_int hTS he, ?_⟩
  exact Finset.dvd_sum fun i hi => bufGcd_dvd (hTS hi)

/-! ## D.37  The exact signed absorber predicate — OPEN -/

/-- **Open node.**  An *exact signed absorber* for the residual `e`: a binary selection of at
most `bound` physically compatible protected switches whose signed increments sum to `e`
exactly.  This predicate is **not inhabited** anywhere in this project. -/
def ExactSignedAbsorber (a M : ℕ) (eps : ℕ → Bool) (e : ℚ) (S : Finset ℕ)
    (outSite innSite : ℕ → ℕ) (bound : ℕ) : Prop :=
  ∃ T ⊆ S, T.card ≤ bound ∧
    (∑ i ∈ T, (1 / (innSite i : ℚ) - 1 / (outSite i : ℚ))) = e ∧
    (∀ i ∈ T, ProtectedSwitch a M eps (outSite i) (innSite i))

/-- **`exactSignedAbsorber_lattice_necessary`.**  `KERNEL-PROVED`.  Any exact signed absorber
satisfies the two lattice conditions, so the conditions are genuine obstructions to inhabiting
the predicate. -/
theorem exactSignedAbsorber_lattice_necessary {a M : ℕ} {eps : ℕ → Bool} {e : ℚ} {S : Finset ℕ}
    {outSite innSite : ℕ → ℕ} {bound : ℕ}
    (h : ExactSignedAbsorber a M eps e S outSite innSite bound) :
    ∃ m : ℤ,
      ((bufDen S (fun i => 1 / (innSite i : ℚ) - 1 / (outSite i : ℚ)) : ℚ)) * e = (m : ℚ) ∧
        bufGcd S (fun i => 1 / (innSite i : ℚ) - 1 / (outSite i : ℚ)) ∣ m := by
  obtain ⟨T, hTS, -, hsum, -⟩ := h
  exact absorber_lattice_necessary hTS hsum.symm

/-- **`absorber_switches_shift_value`.**  `KERNEL-PROVED`.  A one-element absorber does move
the reciprocal value by exactly its increment, so the predicate has the intended meaning. -/
theorem absorber_switches_shift_value {a M : ℕ} {eps : ℕ → Bool} {out inn : ℕ}
    (hs : ProtectedSwitch a M eps out inn) :
    recipSum (selected a M (toggle eps out inn)) - recipSum (selected a M eps)
      = 1 / (inn : ℚ) - 1 / (out : ℚ) := by
  rw [recipSum_toggle hs]
  ring

end Direct
end Erdos287
