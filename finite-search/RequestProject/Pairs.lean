import RequestProject.Defs

/-!
# Constructing window pair supplies

The main construction: if `q > 11` is prime and `P = 2 * q - 1` is prime, then for every
`M` with `P + 1 ≤ M ≤ 2 * P` we have `WindowPairSupply M`, using the window pair

* `x = P`, forbidden by the prime `P` itself (multiplier window `2`);
* `x + 1 = 2 * q`, forbidden by the prime `q` (multiplier window `3`).

Small values of `M` are covered by a handful of hand-made window pairs and by a finite check.
-/

namespace Erdos287

open Finset

/-- A positive natural number smaller than `p` is not divisible by `p`. -/
theorem not_dvd_of_pos_of_lt {p s : ℕ} (h0 : 0 < s) (h : s < p) : ¬ p ∣ s := fun hd =>
  absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- Building a `ForbiddenPP` certificate when the *total* multiplier sum `S` is smaller than `p`.
This is the easy sufficient condition; it applies whenever `p` is large compared to the
window width. -/
theorem forbiddenPP_of_sum_lt {M p a w L S : ℕ} (hp : p.Prime) (ha : 0 < a) (hw : 1 ≤ w)
    (hM : M < (w + 1) * p ^ a) (hL0 : 0 < L)
    (hLdvd : ∀ j ∈ Finset.Icc 1 w, j ∣ L)
    (hS : ∑ j ∈ Finset.Icc 1 w, L / j = S) (hSp : S < p) :
    ForbiddenPP M p a w L := by
  have hterm : ∀ j ∈ Finset.Icc 1 w, 0 < L / j := by
    intro j hj
    exact Nat.div_pos (Nat.le_of_dvd hL0 (hLdvd j hj)) (Finset.mem_Icc.1 hj).1
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 w := Finset.mem_Icc.2 ⟨le_refl 1, hw⟩
  have hLle : L ≤ S := by
    rw [← hS]
    have := Finset.single_le_sum (f := fun j => L / j) (fun j _ => Nat.zero_le _) h1mem
    simpa using this
  refine ⟨hp, ha, hM, hL0, hLdvd, not_dvd_of_pos_of_lt hL0 (by omega), ?_⟩
  intro J hJ hJne
  rw [Finset.mem_powerset] at hJ
  obtain ⟨j₀, hj₀⟩ := hJne
  have hpos : 0 < ∑ j ∈ J, L / j :=
    lt_of_lt_of_le (hterm j₀ (hJ hj₀))
      (Finset.single_le_sum (f := fun j => L / j) (fun j _ => Nat.zero_le _) hj₀)
  have hle : (∑ j ∈ J, L / j) ≤ S := by
    rw [← hS]
    exact Finset.sum_le_sum_of_subset hJ
  exact not_dvd_of_pos_of_lt hpos (by omega)

/--
**Main construction.**  If `q > 11` and `P = 2 * q - 1` are both prime, then every `M` with
`P + 1 ≤ M ≤ 2 * P` admits a window pair supply.
-/
theorem windowPairSupply_of_prime_pair {q P M : ℕ} (hq : q.Prime) (hq11 : 11 < q)
    (hP : P = 2 * q - 1) (hPp : P.Prime) (h1 : P + 1 ≤ M) (h2 : M ≤ 2 * P) :
    WindowPairSupply M := by
  have hqpos : 0 < q := hq.pos
  have hPval : P = 2 * q - 1 := hP
  have hPq : P + 1 = 2 * q := by omega
  have hPbig : 23 ≤ P := by omega
  refine ⟨P, P, 1, 2, 2, q, 1, 3, 6, h1, h2, ?_, ?_, ?_, ?_⟩
  · refine forbiddenPP_of_sum_lt (S := 3) hPp one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by omega)
    rw [pow_one]; omega
  · rw [pow_one]
  · refine forbiddenPP_of_sum_lt (S := 11) hq one_pos (by norm_num) ?_ (by norm_num)
      (by decide) (by decide) (by omega)
    rw [pow_one]; omega
  · rw [hPq, pow_one]
    exact ⟨2, by ring⟩

end Erdos287
