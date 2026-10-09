import Mathlib

/-!
# Anchored V3 — distinctness and AP-free mobility

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Let `n : Fin H → ℕ` be pairwise coprime mobility denominators, each carrying a **private prime**
`p i ∣ n i` with `p i ∤ n j` for `j ≠ i`.  Put

```
G = ∏ i, n i,      a i = ∏_{k ≠ i} n k  (= G / n i),      W c = ∑ i, c i * a i.
```

Reducing modulo the private prime `p i` isolates the `i`-th coefficient.  This yields:

1. **Boolean injectivity** — all `2 ^ H` Boolean subset sums are distinct;
2. **No nontrivial three-term arithmetic progression** — if `W y + W z = 2 * W w` for Boolean
   `y, z, w` then `y = z = w` (private primes taken `≥ 3`);
3. the exact combinatorial identities `#A = 2 ^ H` and `#(A + A) = 3 ^ H`.

## NEGATIVE STRUCTURE INFORMATION

These results are *negative*: many movable targets do **not** produce a long arithmetic
progression or an interval.  Nothing here asserts that mobility can hit a prescribed target.
The additive-energy identity `6 ^ H` is *not* banked.
-/

open scoped BigOperators Pointwise

namespace Erdos287
namespace AnchoredV3

/-- Mobility denominators with private primes. -/
structure MobilityFamily (H : ℕ) where
  /-- the mobility denominators -/
  n : Fin H → ℕ
  /-- denominators are positive -/
  hpos : ∀ i, 0 < n i
  /-- pairwise coprimality -/
  hcop : ∀ i j, i ≠ j → Nat.Coprime (n i) (n j)
  /-- the private prime of each denominator -/
  p : Fin H → ℕ
  /-- private primes are primes, taken at least `3` -/
  hp : ∀ i, (p i).Prime
  /-- private primes are odd (at least `3`) -/
  hp3 : ∀ i, 3 ≤ p i
  /-- the private prime divides its own denominator -/
  hpd : ∀ i, p i ∣ n i
  /-- the private prime divides no other denominator -/
  hpnd : ∀ i j, j ≠ i → ¬ (p i ∣ n j)

namespace MobilityFamily

variable {H : ℕ} (F : MobilityFamily H)

/-- The product of all mobility denominators. -/
def G : ℕ := ∏ i, F.n i

/-- The cofactor `a i = ∏_{k ≠ i} n k`. -/
def a (i : Fin H) : ℕ := ∏ k ∈ Finset.univ.erase i, F.n k

theorem n_mul_a (i : Fin H) : F.n i * F.a i = F.G :=
  Finset.mul_prod_erase _ _ (Finset.mem_univ i)

theorem a_dvd_G (i : Fin H) : F.a i ∣ F.G := ⟨F.n i, by rw [← F.n_mul_a i]; ring⟩

/-- The private prime of `i` divides every other cofactor. -/
theorem p_dvd_a_of_ne {i j : Fin H} (hij : i ≠ j) : F.p i ∣ F.a j :=
  dvd_trans (F.hpd i) (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩))

/-- The private prime of `i` does not divide its own cofactor. -/
theorem p_not_dvd_a (i : Fin H) : ¬ (F.p i ∣ F.a i) := by
  intro hdvd
  obtain ⟨k, hk, hkd⟩ := ((F.hp i).prime.dvd_finset_prod_iff _).mp hdvd
  exact F.hpnd i k (Finset.mem_erase.mp hk).1 hkd

/-- The integer output of a coefficient vector. -/
def W (c : Fin H → ℕ) : ℕ := ∑ i, c i * F.a i

/-- **Coefficient injectivity modulo the private primes.**  Two coefficient vectors with entries
below the private primes producing the same output are equal. -/
theorem W_injective_of_lt {c c' : Fin H → ℕ} (hc : ∀ i, c i < F.p i) (hc' : ∀ i, c' i < F.p i)
    (h : F.W c = F.W c') : c = c' := by
  funext i
  haveI : Fact (F.p i).Prime := ⟨F.hp i⟩
  have hcast : ((F.W c : ℕ) : ZMod (F.p i)) = ((F.W c' : ℕ) : ZMod (F.p i)) := by
    rw [h]
  simp only [W, Nat.cast_sum, Nat.cast_mul] at hcast
  have hzero : ∀ (d : Fin H → ℕ), ∑ j, (d j : ZMod (F.p i)) * (F.a j : ZMod (F.p i))
      = (d i : ZMod (F.p i)) * (F.a i : ZMod (F.p i)) := by
    intro d
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
    have : ((F.a j : ℕ) : ZMod (F.p i)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (F.p_dvd_a_of_ne (Ne.symm hji))
    rw [this, mul_zero]
  rw [hzero c, hzero c'] at hcast
  have hunit : ((F.a i : ℕ) : ZMod (F.p i)) ≠ 0 := by
    intro h0
    exact F.p_not_dvd_a i ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have hci : ((c i : ℕ) : ZMod (F.p i)) = ((c' i : ℕ) : ZMod (F.p i)) :=
    mul_right_cancel₀ hunit hcast
  have := (ZMod.natCast_eq_natCast_iff' (c i) (c' i) (F.p i)).mp hci
  rw [Nat.mod_eq_of_lt (hc i), Nat.mod_eq_of_lt (hc' i)] at this
  exact this

/-- **Boolean injectivity**: all `2 ^ H` Boolean subset sums are distinct. -/
theorem W_injective_boolean {c c' : Fin H → ℕ} (hc : ∀ i, c i ≤ 1) (hc' : ∀ i, c' i ≤ 1)
    (h : F.W c = F.W c') : c = c' := by
  refine F.W_injective_of_lt (fun i => ?_) (fun i => ?_) h
  · have := F.hp3 i; have := hc i; omega
  · have := F.hp3 i; have := hc' i; omega

theorem W_add (c c' : Fin H → ℕ) : F.W c + F.W c' = F.W (fun i => c i + c' i) := by
  simp only [W, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem W_two_mul (c : Fin H → ℕ) : 2 * F.W c = F.W (fun i => 2 * c i) := by
  simp only [W, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **No nontrivial three-term arithmetic progression** in the Boolean mobility family. -/
theorem no_three_term_ap {y z w : Fin H → ℕ} (hy : ∀ i, y i ≤ 1) (hz : ∀ i, z i ≤ 1)
    (hw : ∀ i, w i ≤ 1) (h : F.W y + F.W z = 2 * F.W w) :
    y = z ∧ y = w := by
  have hsum : F.W (fun i => y i + z i) = F.W (fun i => 2 * w i) := by
    rw [← F.W_add, ← F.W_two_mul]
    exact h
  have heq : (fun i => y i + z i) = (fun i => 2 * w i) := by
    refine F.W_injective_of_lt (fun i => ?_) (fun i => ?_) hsum
    · have := F.hp3 i; have := hy i; have := hz i; omega
    · have := F.hp3 i; have := hw i; omega
  constructor
  · funext i
    have := congrFun heq i
    have h1 := hy i; have h2 := hz i; have h3 := hw i
    omega
  · funext i
    have := congrFun heq i
    have h1 := hy i; have h2 := hz i; have h3 := hw i
    omega

/-- The Boolean mobility target set. -/
def targets : Finset ℕ :=
  (Fintype.piFinset (fun _ : Fin H => ({0, 1} : Finset ℕ))).image F.W

/-- **There are exactly `2 ^ H` distinct mobility targets.** -/
theorem card_targets : F.targets.card = 2 ^ H := by
  classical
  rw [targets, Finset.card_image_of_injOn, Fintype.card_piFinset]
  · simp
  · intro c hc c' hc' h
    refine F.W_injective_boolean (fun i => ?_) (fun i => ?_) h
    · have := Fintype.mem_piFinset.mp hc i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' <;> omega
    · have := Fintype.mem_piFinset.mp hc' i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h' <;> omega

/-- **The sumset of the mobility target set has exactly `3 ^ H` elements.** -/
theorem card_targets_add_targets : (F.targets + F.targets).card = 3 ^ H := by
  classical
  have hset : F.targets + F.targets
      = (Fintype.piFinset (fun _ : Fin H => ({0, 1, 2} : Finset ℕ))).image F.W := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨fun i => c i + c' i, ?_, (F.W_add c c').symm⟩
      refine Fintype.mem_piFinset.mpr (fun i => ?_)
      have h1 := Fintype.mem_piFinset.mp hc i
      have h2 := Fintype.mem_piFinset.mp hc' i
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
      omega
    · intro hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      have hcb : ∀ i, c i ≤ 2 := by
        intro i
        have := Fintype.mem_piFinset.mp hc i
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
      refine Finset.mem_add.mpr ⟨F.W (fun i => min (c i) 1), ?_, F.W (fun i => c i - min (c i) 1),
        ?_, ?_⟩
      · refine Finset.mem_image.mpr ⟨fun i => min (c i) 1, ?_, rfl⟩
        refine Fintype.mem_piFinset.mpr (fun i => ?_)
        have := hcb i
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · refine Finset.mem_image.mpr ⟨fun i => c i - min (c i) 1, ?_, rfl⟩
        refine Fintype.mem_piFinset.mpr (fun i => ?_)
        have := hcb i
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · rw [F.W_add]
        congr 1
        funext i
        have := hcb i
        omega
  rw [hset, Finset.card_image_of_injOn, Fintype.card_piFinset]
  · simp
  · intro c hc c' hc' h
    refine F.W_injective_of_lt (fun i => ?_) (fun i => ?_) h
    · have := Fintype.mem_piFinset.mp hc i
      have h3 := F.hp3 i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    · have := Fintype.mem_piFinset.mp hc' i
      have h3 := F.hp3 i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega

/-- **The cofactors are globally coprime.**  For `H ≥ 1` the gcd of the cofactors `a i` is `1`;
this is the exact statement behind the mobility congruence coset. -/
theorem gcd_cofactors_eq_one (hH : 0 < H) : (Finset.univ.gcd F.a) = 1 := by
  classical
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hi : (⟨0, hH⟩ : Fin H) ∈ (Finset.univ : Finset (Fin H)) := Finset.mem_univ _
  have hra : ∀ i : Fin H, r ∣ F.a i := fun i => hrd.trans (Finset.gcd_dvd (Finset.mem_univ i))
  obtain ⟨k, hk, hkd⟩ := (hr.prime.dvd_finset_prod_iff _).mp (hra ⟨0, hH⟩)
  obtain ⟨j, hj, hjd⟩ := (hr.prime.dvd_finset_prod_iff _).mp (hra k)
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hcop := F.hcop k j (Ne.symm hjk)
  have : r ∣ Nat.gcd (F.n k) (F.n j) := Nat.dvd_gcd hkd hjd
  rw [hcop] at this
  exact hr.one_lt.ne' (Nat.dvd_one.mp this)

end MobilityFamily

end AnchoredV3
end Erdos287
