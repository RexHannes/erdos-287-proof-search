import Mathlib

/-!
# Erdős #287 — physical source: exact CRT and modular-inverse lemmas

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Exact elementary number theory used by
the physical packet construction (`sources/physical_spec.md`, §§9–10).

* `crt_int` — a finite system `x ≡ r_i (mod m_i)` with pairwise coprime positive moduli is
  equivalent to the single congruence `x ≡ c (mod ∏ m_i)` for some `c < ∏ m_i`.
* `gcdA_inv` — `a · gcdA(a,m) ≡ 1 (mod m)` when `(a,m) = 1`: the explicit Bézout inverse
  used for every `a⁻¹` in the source.
* `mul_congr_iff_inv` — for `(a,m)=1`: `a x ≡ a - a' (mod m) ↔ x ≡ 1 - a'·a⁻¹ (mod m)`.
* `dvd_mul_cancel_coprime` — `e ∣ g y ↔ e ∣ y` when `(g,e)=1`.
-/

open scoped BigOperators
open Finset

namespace Erdos287.Physical

/-- **Exact CRT over a finset, integer residues.** -/
theorem crt_int {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (pw : (s : Set ι).Pairwise (Function.onFun Nat.Coprime m)) :
    ∃ c : ℕ, c < ∏ i ∈ s, m i ∧
      ∀ x : ℤ, (∀ i ∈ s, x ≡ r i [ZMOD m i]) ↔ x ≡ c [ZMOD (∏ i ∈ s, m i : ℕ)] := by
  set a : ι → ℕ := fun i => (r i % m i).toNat
  have hne : ∀ i ∈ s, m i ≠ 0 := fun i hi => (hm i hi).ne'
  let K := Nat.chineseRemainderOfFinset a m s hne pw
  have hk := K.2
  have hlt : (K : ℕ) < ∏ i ∈ s, m i := Nat.chineseRemainderOfFinset_lt_prod a m hne pw
  have hkr : ∀ i ∈ s, ((K : ℕ) : ℤ) ≡ r i [ZMOD m i] := by
    intro i hi
    have h1 : ((K : ℕ) : ℤ) ≡ ((a i : ℕ) : ℤ) [ZMOD m i] := (Int.natCast_modEq_iff).mpr (hk i hi)
    have h2 : ((a i : ℕ) : ℤ) = r i % m i := by
      simp only [a]; rw [Int.toNat_of_nonneg]; exact Int.emod_nonneg _ (by exact_mod_cast hne i hi)
    rw [h2] at h1
    exact h1.trans (Int.mod_modEq _ _)
  refine ⟨K, hlt, fun x => ⟨fun h => ?_, fun h i hi => ?_⟩⟩
  · rw [Int.modEq_iff_dvd]
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Nat.isCoprime_iff_coprime.mpr (pw hi hj hij)
    · intro i hi
      exact Int.modEq_iff_dvd.mp ((h i hi).trans (hkr i hi).symm)
  · have hd : (m i : ℤ) ∣ ((∏ i ∈ s, m i : ℕ) : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem m hi
    exact (Int.ModEq.of_dvd hd h).trans (hkr i hi)

/-- The explicit Bézout inverse: `a · gcdA(a,m) ≡ 1 (mod m)` for coprime `a, m`. -/
theorem gcdA_inv {a m : ℕ} (h : Nat.Coprime a m) : (a : ℤ) * Nat.gcdA a m ≡ 1 [ZMOD m] := by
  have := Nat.gcd_eq_gcd_ab a m
  rw [h] at this
  rw [Int.modEq_iff_dvd]
  exact ⟨Nat.gcdB a m, by push_cast at this; linarith⟩

/-- `a x ≡ a - a' (mod m) ↔ x ≡ 1 - a' a⁻¹ (mod m)` for `(a, m) = 1`. -/
theorem mul_congr_iff_inv {a a' m : ℕ} (h : Nat.Coprime a m) (x : ℤ) :
    (a : ℤ) * x ≡ a - a' [ZMOD m] ↔ x ≡ 1 - a' * Nat.gcdA a m [ZMOD m] := by
  have hu := gcdA_inv h
  constructor
  · intro hx
    have h1 : (Nat.gcdA a m : ℤ) * (a * x) ≡ Nat.gcdA a m * (a - a') [ZMOD m] := hx.mul_left _
    have h2 : x ≡ (Nat.gcdA a m : ℤ) * (a * x) [ZMOD m] := by
      have := (hu.mul_right x).symm
      calc x = 1 * x := by ring
        _ ≡ (a * Nat.gcdA a m) * x [ZMOD m] := this
        _ = _ := by ring
    have h3 : (Nat.gcdA a m : ℤ) * (a - a') ≡ 1 - a' * Nat.gcdA a m [ZMOD m] := by
      have := (hu.sub_right (a' * Nat.gcdA a m))
      calc (Nat.gcdA a m : ℤ) * (a - a') = a * Nat.gcdA a m - a' * Nat.gcdA a m := by ring
        _ ≡ _ [ZMOD m] := this
    exact h2.trans (h1.trans h3)
  · intro hx
    have h1 := hx.mul_left (a : ℤ)
    have h2 : (a : ℤ) * (1 - a' * Nat.gcdA a m) ≡ a - a' [ZMOD m] := by
      have := (hu.mul_left (a' : ℤ)).neg.add_left (a : ℤ)
      calc (a : ℤ) * (1 - a' * Nat.gcdA a m) = a + -(a' * (a * Nat.gcdA a m)) := by ring
        _ ≡ a + -(a' * 1) [ZMOD m] := this
        _ = _ := by ring
    exact h1.trans h2

/-- Cancellation of a factor coprime to the modulus. -/
theorem dvd_mul_cancel_coprime {g e : ℕ} (h : Nat.Coprime g e) (y : ℤ) :
    (e : ℤ) ∣ g * y ↔ (e : ℤ) ∣ y := by
  constructor
  · intro hd
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hd (by rw [Int.gcd_comm]; exact_mod_cast h)
  · intro hd; exact Dvd.dvd.mul_left hd _

/-- Two-modulus CRT in the form used for `b_{ξ,d}`: for coprime `f, e > 0`, a residue `c` mod
`f` and a residue `r` mod `e`, there is `b < f e` with
`(x ≡ c [f] ∧ x ≡ r [e]) ↔ x ≡ b [f e]`. -/
theorem crt_two {f e : ℕ} (hf : 0 < f) (he : 0 < e) (hfe : Nat.Coprime f e) (c r : ℤ) :
    ∃ b : ℕ, b < f * e ∧ ∀ x : ℤ, (x ≡ c [ZMOD f] ∧ x ≡ r [ZMOD e]) ↔ x ≡ b [ZMOD (f * e : ℕ)] := by
  classical
  obtain ⟨b, hb, hiff⟩ := crt_int (Finset.univ : Finset Bool) (fun t => if t then f else e)
    (fun t => if t then c else r) (by intro t _; cases t <;> simp [hf, he])
    (by
      intro s _ t _ hst
      cases s <;> cases t
      · exact absurd rfl hst
      · exact hfe.symm
      · exact hfe
      · exact absurd rfl hst)
  have hprod : (∏ t : Bool, (if t then f else e)) = f * e := by
    rw [Fintype.prod_bool]; simp
  refine ⟨b, by simpa [hprod] using hb, fun x => ?_⟩
  have := hiff x
  rw [hprod] at this
  rw [← this]
  constructor
  · rintro ⟨h1, h2⟩ t _; cases t <;> simp [h1, h2]
  · intro h; exact ⟨by simpa using h true (by simp), by simpa using h false (by simp)⟩

end Erdos287.Physical
