import RequestProject.Erdos287.AnchoredV2.UnitSubsetSum

/-!
# Anchored V3 — the Boolean column gcd theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Let `q ≥ 2` and let `a i` (`i ∈ s`) be positive `q`-units, i.e. `gcd (a i) q = 1`.  A **zero
pattern** is a subset `E ⊆ s` with `q ∣ ∑_{i ∈ E} a i`; its **integer weight** is
`w E = (∑_{i ∈ E} a i) / q`.

The sharp finite theorem proved here is: if

```
#s ≥ 2 q - 1,
```

then

```
gcd { w E : E a zero pattern } = gcd { a i : i ∈ s }.
```

The nontrivial inclusion is proved by the **constructive telescoping certificate**: for a pivot
`i` and two disjoint groups `A, B` of `q - 1` other entries, the finite unit subset-sum theorem
(Anchored V2, `exists_subset_sum_eq`) supplies subsets `S t ⊆ A` and `T u ⊆ B` realising every
residue, and with

```
E⁰_{i,t} = S t ∪ T (-t),        E⁺_{i,t} = {i} ∪ S (t - a_i) ∪ T (-t)
```

one has the exact identity

```
a i = ∑_{t ∈ ZMod q} ( w E⁺_{i,t} - w E⁰_{i,t} ),
```

because `t ↦ t - a_i` permutes `ZMod q`.

## FIREWALL

This is a statement about the **integer span / gcd** of zero-pattern weights.  It does *not*
construct a Boolean selection hitting an arbitrary target: the patterns above overlap and the
identity uses subtraction.  `sharpness_witness_two` shows the hypothesis `#s ≥ 2q - 1` is sharp:
at `n = 2q - 2` the raw gcd can be `1` while the zero-pattern weight gcd is `2`.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV3
namespace ColumnLattice

/-- Divisibility of a natural sum by `q` in terms of the `ZMod q` sum. -/
theorem cast_sum_eq_zero_iff {q : ℕ} (a : ℕ → ℕ) (E : Finset ℕ) :
    (∑ j ∈ E, (a j : ZMod q)) = 0 ↔ q ∣ ∑ j ∈ E, a j := by
  rw [← Nat.cast_sum]
  exact ZMod.natCast_eq_zero_iff _ _

/-- The `Finset` form of the Anchored V2 unit subset-sum theorem. -/
theorem exists_subset_sum_eq_finset {q : ℕ} (hq : 2 ≤ q) {A : Finset ℕ} (hA : q - 1 ≤ A.card)
    (c : ℕ → ZMod q) (hc : ∀ j ∈ A, IsUnit (c j)) (t : ZMod q) :
    ∃ S ⊆ A, ∑ j ∈ S, c j = t := by
  classical
  have hn : A.card = A.card := rfl
  set e := A.orderIsoOfFin hn with he
  have hmem : ∀ k : Fin A.card, ((e k : ℕ)) ∈ A := fun k => (e k).2
  obtain ⟨I, hI⟩ := Erdos287.AnchoredV2.exists_subset_sum_eq hq hA
      (fun k => c (e k)) (fun k => hc _ (hmem k)) t
  have hinj : ∀ x ∈ I, ∀ y ∈ I, ((e x : ℕ)) = ((e y : ℕ)) → x = y := by
    intro x _ y _ hxy
    exact e.injective (Subtype.ext hxy)
  refine ⟨I.image (fun k => (e k : ℕ)), ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact hmem k
  · rw [Finset.sum_image hinj]
    exact hI

variable (q : ℕ) (a : ℕ → ℕ) (s : Finset ℕ)

/-- The finite set of column zero patterns inside `s`. -/
def zeroPatterns : Finset (Finset ℕ) := s.powerset.filter (fun E => q ∣ ∑ i ∈ E, a i)

/-- The integer weight of a pattern. -/
def weight (E : Finset ℕ) : ℕ := (∑ i ∈ E, a i) / q

/-- The finite set of zero-pattern weights. -/
def patternWeights : Finset ℕ := (zeroPatterns q a s).image (weight q a)

variable {q a s}

theorem mem_patternWeights {E : Finset ℕ} (hEs : E ⊆ s) (hdvd : q ∣ ∑ i ∈ E, a i) :
    weight q a E ∈ patternWeights q a s := by
  classical
  refine Finset.mem_image.mpr ⟨E, ?_, rfl⟩
  simp only [zeroPatterns, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hEs, hdvd⟩

theorem gcd_dvd_weight {E : Finset ℕ} (hEs : E ⊆ s) (hdvd : q ∣ ∑ i ∈ E, a i) :
    (patternWeights q a s).gcd id ∣ weight q a E :=
  Finset.gcd_dvd (mem_patternWeights hEs hdvd)

theorem q_mul_weight {E : Finset ℕ} (hdvd : q ∣ ∑ i ∈ E, a i) :
    q * weight q a E = ∑ i ∈ E, a i :=
  Nat.mul_div_cancel' hdvd

/-- **Easy inclusion**: the coefficient gcd divides every zero-pattern weight. -/
theorem coeff_gcd_dvd_patternWeights_gcd (hq : 2 ≤ q) (hcop : ∀ i ∈ s, Nat.Coprime (a i) q)
    (hne : s.Nonempty) : s.gcd a ∣ (patternWeights q a s).gcd id := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  have hgq : Nat.Coprime (s.gcd a) q :=
    Nat.Coprime.coprime_dvd_left (Finset.gcd_dvd hi₀) (hcop i₀ hi₀)
  refine Finset.dvd_gcd ?_
  intro w hw
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hw
  simp only [zeroPatterns, Finset.mem_filter, Finset.mem_powerset] at hE
  obtain ⟨hEs, hdvd⟩ := hE
  have hgS : s.gcd a ∣ ∑ i ∈ E, a i :=
    Finset.dvd_sum (fun i hi => Finset.gcd_dvd (hEs hi))
  have hmul : q * s.gcd a ∣ ∑ i ∈ E, a i :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hgq.symm hdvd hgS
  obtain ⟨k, hk⟩ := hmul
  have hqpos : 0 < q := by omega
  have : weight q a E = s.gcd a * k := by
    simp only [weight, hk, mul_assoc]
    exact Nat.mul_div_cancel_left _ hqpos
  exact ⟨k, this⟩

/-- **The constructive telescoping certificate.**  With at least `2q - 1` unit coefficients the
gcd of the zero-pattern weights divides every coefficient. -/
theorem gcd_patternWeights_dvd_coeff (hq : 2 ≤ q) (hcop : ∀ i ∈ s, Nat.Coprime (a i) q)
    (hcard : 2 * q - 1 ≤ s.card) {i : ℕ} (hi : i ∈ s) :
    (patternWeights q a s).gcd id ∣ a i := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  set d := (patternWeights q a s).gcd id with hd
  -- two disjoint groups of `q - 1` further coefficients
  have hcarderase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (show q - 1 ≤ (s.erase i).card by omega)
  have hsdiff : ((s.erase i) \ A).card = (s.erase i).card - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub]
  obtain ⟨B, hBsub, hBcard⟩ :=
    Finset.exists_subset_card_eq (show q - 1 ≤ ((s.erase i) \ A).card by omega)
  have hBerase : B ⊆ s.erase i := hBsub.trans Finset.sdiff_subset
  have hAs : A ⊆ s := hAsub.trans (Finset.erase_subset _ _)
  have hBs : B ⊆ s := hBerase.trans (Finset.erase_subset _ _)
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hBsub hxB)).2 hxA
  have hiA : i ∉ A := fun h => (Finset.mem_erase.mp (hAsub h)).1 rfl
  have hiB : i ∉ B := fun h => (Finset.mem_erase.mp (hBerase h)).1 rfl
  -- all coefficients are units mod q
  have hunit : ∀ j ∈ s, IsUnit ((a j : ZMod q)) := by
    intro j hj
    exact (ZMod.isUnit_iff_coprime (a j) q).mpr (hcop j hj)
  -- residue-realising subsets of A and of B
  have hSex : ∀ t : ZMod q, ∃ S ⊆ A, ∑ j ∈ S, (a j : ZMod q) = t := by
    intro t
    exact exists_subset_sum_eq_finset hq (by omega) (fun j => (a j : ZMod q))
      (fun j hj => hunit j (hAs hj)) t
  have hTex : ∀ t : ZMod q, ∃ T ⊆ B, ∑ j ∈ T, (a j : ZMod q) = t := by
    intro t
    exact exists_subset_sum_eq_finset hq (by omega) (fun j => (a j : ZMod q))
      (fun j hj => hunit j (hBs hj)) t
  choose S hSsub hSsum using hSex
  choose T hTsub hTsum using hTex
  set ai : ZMod q := (a i : ZMod q) with hai
  set σ : ZMod q → ℕ := fun t => ∑ j ∈ S t, a j with hσ
  set τ : ZMod q → ℕ := fun t => ∑ j ∈ T t, a j with hτ
  -- the two families of zero patterns
  set E0 : ZMod q → Finset ℕ := fun t => S t ∪ T (-t) with hE0
  set E1 : ZMod q → Finset ℕ := fun t => insert i (S (t - ai) ∪ T (-t)) with hE1
  have hdisjST : ∀ t u : ZMod q, Disjoint (S t) (T u) := by
    intro t u
    exact Finset.disjoint_of_subset_left (hSsub t)
      (Finset.disjoint_of_subset_right (hTsub u) hAB)
  have hsumE0 : ∀ t, ∑ j ∈ E0 t, a j = σ t + τ (-t) := by
    intro t
    simpa [hE0, hσ, hτ] using Finset.sum_union (hdisjST t (-t)) (f := a)
  have hnotmem : ∀ t u : ZMod q, i ∉ S t ∪ T u := by
    intro t u hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact hiA (hSsub t h)
    · exact hiB (hTsub u h)
  have hsumE1 : ∀ t, ∑ j ∈ E1 t, a j = a i + (σ (t - ai) + τ (-t)) := by
    intro t
    rw [hE1, Finset.sum_insert (hnotmem (t - ai) (-t))]
    congr 1
    simpa [hσ, hτ] using Finset.sum_union (hdisjST (t - ai) (-t)) (f := a)
  -- both families are zero patterns
  have hE0sub : ∀ t, E0 t ⊆ s := by
    intro t
    exact Finset.union_subset ((hSsub t).trans hAs) ((hTsub (-t)).trans hBs)
  have hE1sub : ∀ t, E1 t ⊆ s := by
    intro t
    exact Finset.insert_subset hi
      (Finset.union_subset ((hSsub (t - ai)).trans hAs) ((hTsub (-t)).trans hBs))
  have hE0dvd : ∀ t, q ∣ ∑ j ∈ E0 t, a j := by
    intro t
    rw [← cast_sum_eq_zero_iff]
    rw [hE0, Finset.sum_union (hdisjST t (-t))]
    rw [hSsum t, hTsum (-t)]
    ring
  have hE1dvd : ∀ t, q ∣ ∑ j ∈ E1 t, a j := by
    intro t
    rw [← cast_sum_eq_zero_iff]
    rw [hE1, Finset.sum_insert (hnotmem (t - ai) (-t)),
      Finset.sum_union (hdisjST (t - ai) (-t)), hSsum (t - ai), hTsum (-t), ← hai]
    ring
  -- the exact telescoping identity, first over ℕ multiplied by q
  have hq0 : (0:ℤ) < (q:ℤ) := by exact_mod_cast (by omega : 0 < q)
  have hkey : (q : ℤ) * ∑ t : ZMod q, ((weight q a (E1 t) : ℤ) - (weight q a (E0 t) : ℤ))
      = (q : ℤ) * (a i : ℤ) := by
    have hterm : ∀ t : ZMod q,
        (q : ℤ) * ((weight q a (E1 t) : ℤ) - (weight q a (E0 t) : ℤ))
          = (a i : ℤ) + ((σ (t - ai) : ℤ) - (σ t : ℤ)) := by
      intro t
      have h1 : (q : ℤ) * (weight q a (E1 t) : ℤ) = ((∑ j ∈ E1 t, a j : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (q_mul_weight (hE1dvd t))
      have h0 : (q : ℤ) * (weight q a (E0 t) : ℤ) = ((∑ j ∈ E0 t, a j : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (q_mul_weight (hE0dvd t))
      have e1 : ((∑ j ∈ E1 t, a j : ℕ) : ℤ) = (a i : ℤ) + ((σ (t - ai) : ℤ) + (τ (-t) : ℤ)) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (hsumE1 t)
      have e0 : ((∑ j ∈ E0 t, a j : ℕ) : ℤ) = (σ t : ℤ) + (τ (-t) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (hsumE0 t)
      rw [mul_sub, h1, h0, e1, e0]
      ring
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun t _ => hterm t)]
    rw [Finset.sum_add_distrib]
    have hshift : ∑ t : ZMod q, ((σ (t - ai) : ℤ) - (σ t : ℤ)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have : ∑ t : ZMod q, (σ (t - ai) : ℤ) = ∑ t : ZMod q, (σ t : ℤ) :=
        Fintype.sum_equiv (Equiv.subRight ai) _ _ (fun t => rfl)
      rw [this, sub_self]
    rw [hshift, add_zero, Finset.sum_const]
    have hcardq : (Finset.univ : Finset (ZMod q)).card = q := by
      simp
    rw [hcardq, nsmul_eq_mul]
  have hsum_eq : ∑ t : ZMod q, ((weight q a (E1 t) : ℤ) - (weight q a (E0 t) : ℤ))
      = (a i : ℤ) := mul_left_cancel₀ hq0.ne' hkey
  -- `d` divides each weight, hence the telescoped sum
  have hdvdsum : (d : ℤ) ∣ ∑ t : ZMod q, ((weight q a (E1 t) : ℤ) - (weight q a (E0 t) : ℤ)) := by
    refine Finset.dvd_sum ?_
    intro t _
    refine dvd_sub ?_ ?_
    · exact_mod_cast Int.natCast_dvd_natCast.mpr (gcd_dvd_weight (hE1sub t) (hE1dvd t))
    · exact_mod_cast Int.natCast_dvd_natCast.mpr (gcd_dvd_weight (hE0sub t) (hE0dvd t))
  rw [hsum_eq] at hdvdsum
  exact_mod_cast hdvdsum

/-- **The Boolean column gcd theorem.**  For `q ≥ 2` and at least `2q - 1` positive `q`-units,
the gcd of the zero-pattern weights equals the gcd of the coefficients. -/
theorem boolean_column_gcd (hq : 2 ≤ q) (hcop : ∀ i ∈ s, Nat.Coprime (a i) q)
    (hcard : 2 * q - 1 ≤ s.card) :
    (patternWeights q a s).gcd id = s.gcd a := by
  have hne : s.Nonempty := by
    rw [← Finset.card_pos]
    omega
  refine Nat.dvd_antisymm ?_ (coeff_gcd_dvd_patternWeights_gcd hq hcop hne)
  exact Finset.dvd_gcd (fun i hi => gcd_patternWeights_dvd_coeff hq hcop hcard hi)

/-- The coefficient family of the sharpness witness: `a 0 = 1`, `a 1 = 3`. -/
def sharpCoeff : ℕ → ℕ := fun i => if i = 0 then 1 else 3

/-- **Sharpness at `n = 2q - 2`.**  For `q = 2` and the two coefficients `1, 3` (so
`#s = 2 = 2q - 2`) the raw coefficient gcd is `1`, while the zero-pattern weight gcd is `2`. -/
theorem sharpness_witness_two :
    ({0, 1} : Finset ℕ).gcd sharpCoeff = 1 ∧
      (patternWeights 2 sharpCoeff {0, 1}).gcd id = 2 := by
  constructor
  · decide
  · decide

end ColumnLattice
end AnchoredV3
end Erdos287
