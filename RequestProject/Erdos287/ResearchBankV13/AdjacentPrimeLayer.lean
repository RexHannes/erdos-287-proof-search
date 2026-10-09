import RequestProject.Erdos287.ResearchBankV13.HarmonicTwoHole

/-!
# Erdős #287 — Research Bank V13 §21: adjacent prime-layer certificates (two families)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Family A** (`familyA_interval`): `p = 2q + 1`, `p, q` prime, `q > 137`.  For every endpoint
`p − 1 ≤ M ≤ ⌊(685/252) p⌋`:
* `p` is forbidden (prime layer, `r = p`, `J = 2`, `A 2 = 3 < p`, `M < 3p`);
* `p − 1 = 2q` is forbidden (prime layer, `r = q`, `J = 5`, `A 5 = 137 < q`, `M < 6q`);
so the two-hole theorem excludes the whole interval.

**Family B** (`familyB_interval`): `p = 4q + 1`, `p, q` prime, `q > 7381`.  Same conclusion using
`J = 10` for `q` (`A 10 = 7381 < q`, `M < 11q`) and `J = 2` for `p`.

`familyB_outside_goodPrimeHalf`: for `q > 3`, Family B is genuinely outside the earlier
"good-prime half" class: `(p−1)/2 = 2q` is composite and `(p+1)/2 = 2q+1` is divisible by `3`
and `> 3`.
-/

namespace Erdos287
namespace ResearchBankV13
namespace AdjacentPrimeLayer

open FiniteRepresentationModel PrimeLayer HarmonicTwoHole

/-- **Family A.** -/
theorem familyA_interval {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p = 2 * q + 1)
    (hq137 : 137 < q) :
    ∀ M, p - 1 ≤ M → M ≤ etaFloor p → NoCounterexampleAt M := by
  have hp1 : p - 1 + 1 = p := by omega
  intro M h1 h2
  refine interval_exclusion_of_adjacent_holes (h := p - 1) (lo := p - 1) (hi := etaFloor p)
    le_rfl (by rw [hp1]) ?_ M h1 h2
  intro A hA hlo hhi
  have hhi' : 252 * A.max' hA.nonempty ≤ 685 * p := by unfold etaFloor at hhi; omega
  refine ⟨?_, ?_⟩
  · -- `p − 1 = 2q` is forbidden via the `q`-layer with `J = 5`
    intro hmem
    have hM : A.max' hA.nonempty < (5 + 1) * q := by omega
    exact primeLayer_exclusion hA hq hM (by rw [A_5]; omega) _ hmem
      ⟨2, by omega⟩
  · -- `p` is forbidden via the `p`-layer with `J = 2`
    intro hmem
    have hM : A.max' hA.nonempty < (2 + 1) * p := by omega
    rw [hp1] at hmem
    exact primeLayer_exclusion hA hp hM (by rw [A_2]; omega) _ hmem dvd_rfl

/-- **Family B.** -/
theorem familyB_interval {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p = 4 * q + 1)
    (hq7381 : 7381 < q) :
    ∀ M, p - 1 ≤ M → M ≤ etaFloor p → NoCounterexampleAt M := by
  have hp1 : p - 1 + 1 = p := by omega
  intro M h1 h2
  refine interval_exclusion_of_adjacent_holes (h := p - 1) (lo := p - 1) (hi := etaFloor p)
    le_rfl (by rw [hp1]) ?_ M h1 h2
  intro A hA hlo hhi
  have hhi' : 252 * A.max' hA.nonempty ≤ 685 * p := by unfold etaFloor at hhi; omega
  refine ⟨?_, ?_⟩
  · intro hmem
    have hM : A.max' hA.nonempty < (10 + 1) * q := by omega
    exact primeLayer_exclusion hA hq hM (by rw [A_10]; omega) _ hmem ⟨4, by omega⟩
  · intro hmem
    have hM : A.max' hA.nonempty < (2 + 1) * p := by omega
    rw [hp1] at hmem
    exact primeLayer_exclusion hA hp hM (by rw [A_2]; omega) _ hmem dvd_rfl

/-- **Family B is outside the good-prime-half class** (for `q > 3`). -/
theorem familyB_outside_goodPrimeHalf {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p = 4 * q + 1) (hq3 : 3 < q) :
    (p - 1) / 2 = 2 * q ∧ ¬ (2 * q).Prime ∧ (p + 1) / 2 = 2 * q + 1 ∧ 3 ∣ 2 * q + 1 ∧
      3 < 2 * q + 1 := by
  have hcomp : ¬ (2 * q).Prime := by
    rw [Nat.prime_mul_iff]; omega
  have hq3' : ¬ 3 ∣ q := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h
    omega
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  refine ⟨by omega, hcomp, by omega, ?_, by omega⟩
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hmod with h | h
  · omega
  · exact absurd (by omega : 3 ∣ p) hp3

/-! ## Small kernel-checked instances of the family hypotheses -/

/-- `q = 173`, `p = 347` is a Family-A pair (primality by `norm_num`). -/
theorem familyA_instance : ∀ M, 346 ≤ M → M ≤ etaFloor 347 → NoCounterexampleAt M :=
  familyA_interval (p := 347) (q := 173) (by norm_num) (by norm_num) rfl (by norm_num)

theorem etaFloor_347 : etaFloor 347 = 943 := by decide

end AdjacentPrimeLayer
end ResearchBankV13
end Erdos287
