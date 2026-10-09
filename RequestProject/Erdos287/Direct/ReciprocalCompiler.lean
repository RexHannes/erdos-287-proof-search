import RequestProject.Erdos287.Direct.Core

/-!
# Route D — the exact ambient-LCM reciprocal compiler

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The compiler turns the rational equation `∑_{n∈A} 1/n = 1` into an exact integer equation
over a cleared denominator.  Three denominators are kept apart, as required:

* the **ambient** interval LCM `ambientLcm a M = lcm [a, M]`;
* the **selected-set** LCM `setLcm A`;
* the **free-position** LCM `setLcm V`.

The compiler is proved as an *equivalence*, under the exact hypothesis that the ambient
index set does not contain `0` (this is what makes the cleared denominator nonzero).  The
historical empty-subset bug is not reintroduced: the statement is proved for every subset
`A ⊆ I`, including `A = ∅`, and `compiler_requires_nonzero` shows the hypothesis `0 ∉ I`
cannot be dropped.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.5  The three denominators -/

/-- The LCM of a finite set of positions. -/
def setLcm (A : Finset ℕ) : ℕ := A.lcm id

/-- The ambient interval LCM of `[a, M]`. -/
def ambientLcm (a M : ℕ) : ℕ := setLcm (ambient a M)

theorem dvd_setLcm {A : Finset ℕ} {n : ℕ} (hn : n ∈ A) : n ∣ setLcm A :=
  Finset.dvd_lcm hn

theorem setLcm_dvd_of_subset {A B : Finset ℕ} (h : A ⊆ B) : setLcm A ∣ setLcm B :=
  Finset.lcm_dvd fun _ hn => dvd_setLcm (h hn)

theorem setLcm_ne_zero {A : Finset ℕ} (h0 : 0 ∉ A) : setLcm A ≠ 0 := by
  intro hz
  rw [setLcm, Finset.lcm_eq_zero_iff] at hz
  simp only [id] at hz
  obtain ⟨x, hx, hx0⟩ := hz
  exact h0 (hx0 ▸ hx)

theorem setLcm_pos {A : Finset ℕ} (h0 : 0 ∉ A) : 0 < setLcm A :=
  Nat.pos_of_ne_zero (setLcm_ne_zero h0)

theorem ambientLcm_pos {a M : ℕ} (ha : 0 < a) : 0 < ambientLcm a M := by
  refine setLcm_pos ?_
  simp only [ambient, Finset.mem_Icc]
  omega

/-! ## D.6  The exact cleared-denominator compiler -/

/-- **`clearing_identity`.**  `KERNEL-PROVED`.  The exact cleared-denominator identity for
any index set `A` all of whose members divide `D` and are nonzero. -/
theorem clearing_identity {A : Finset ℕ} {D : ℕ} (hdvd : ∀ n ∈ A, n ∣ D)
    (h0 : ∀ n ∈ A, n ≠ 0) :
    ((∑ n ∈ A, D / n : ℕ) : ℚ) = (D : ℚ) * recipSum A := by
  rw [recipSum, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (h0 n hn)
  rw [Nat.cast_div (hdvd n hn) hn0]
  field_simp

/-- **`compiler_ambient`.**  `KERNEL-PROVED`.  The exact compiler over the ambient LCM: for
every subset `A` of an index set `I` with `0 ∉ I`, the rational equation `∑ 1/n = 1` is
*equivalent* to the integer equation `∑ D/n = D`. -/
theorem compiler_ambient {I : Finset ℕ} (h0 : 0 ∉ I) {A : Finset ℕ} (hA : A ⊆ I) :
    recipSum A = 1 ↔ ∑ n ∈ A, setLcm I / n = setLcm I := by
  have hD : (setLcm I : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (setLcm_ne_zero h0)
  have key := clearing_identity (A := A) (D := setLcm I)
    (fun n hn => dvd_setLcm (hA hn)) (fun n hn h => h0 (h ▸ hA hn))
  constructor
  · intro h
    have : ((∑ n ∈ A, setLcm I / n : ℕ) : ℚ) = (setLcm I : ℚ) := by rw [key, h, mul_one]
    exact_mod_cast this
  · intro h
    have h' : ((∑ n ∈ A, setLcm I / n : ℕ) : ℚ) = (setLcm I : ℚ) := by exact_mod_cast h
    rw [key] at h'
    field_simp at h'
    exact h'

/-- **`compiler_interval`.**  `KERNEL-PROVED`.  The compiler specialised to the Route-D
ambient interval `[a, M]` with `a ≥ 1`. -/
theorem compiler_interval {a M : ℕ} (ha : 0 < a) (eps : ℕ → Bool) :
    recipSum (selected a M eps) = 1 ↔
      ∑ n ∈ selected a M eps, ambientLcm a M / n = ambientLcm a M := by
  have h0 : (0 : ℕ) ∉ ambient a M := by simp only [ambient, Finset.mem_Icc]; omega
  exact compiler_ambient h0 (selected_subset_ambient a M eps)

/-- **`compiler_selected_lcm`.**  `KERNEL-PROVED`.  The same equivalence over the *selected
set's own* LCM, which is in general a proper divisor of the ambient one. -/
theorem compiler_selected_lcm {A : Finset ℕ} (h0 : 0 ∉ A) :
    recipSum A = 1 ↔ ∑ n ∈ A, setLcm A / n = setLcm A :=
  compiler_ambient h0 (subset_refl A)

/-- **`selected_lcm_dvd_ambient`.**  `KERNEL-PROVED`.  The three denominators are ordered by
divisibility: free-position LCM ∣ selected LCM ∣ ambient LCM, whenever the corresponding
inclusions hold. -/
theorem selected_lcm_dvd_ambient {a M : ℕ} (eps : ℕ → Bool) :
    setLcm (selected a M eps) ∣ ambientLcm a M :=
  setLcm_dvd_of_subset (selected_subset_ambient a M eps)

/-! ## D.7  Firewalls: the hypotheses are not decoration -/

/-- **`compiler_empty_consistent`.**  `KERNEL-PROVED`.  On the empty subset both sides of the
compiler are false (there is no empty-subset bug): `recipSum ∅ = 0 ≠ 1` and `0 ≠ D` because
`D > 0`. -/
theorem compiler_empty_consistent {I : Finset ℕ} (h0 : 0 ∉ I) :
    recipSum (∅ : Finset ℕ) ≠ 1 ∧ (∑ n ∈ (∅ : Finset ℕ), setLcm I / n) ≠ setLcm I := by
  refine ⟨by simp, ?_⟩
  simpa using (setLcm_ne_zero h0).symm

/-- **`compiler_requires_nonzero`.**  `KERNEL-PROVED` firewall.  The hypothesis `0 ∉ I` is
necessary: for `I = {0}` and `A = ∅` the cleared equation holds while the rational equation
fails, so the equivalence is false without it. -/
theorem compiler_requires_nonzero :
    (∑ n ∈ (∅ : Finset ℕ), setLcm {0} / n) = setLcm {0} ∧
      recipSum (∅ : Finset ℕ) ≠ 1 := by
  refine ⟨?_, by simp⟩
  simp [setLcm]

end Direct
end Erdos287
