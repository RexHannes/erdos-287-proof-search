import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the small-`ℓ` complete local formula and its CRT expansion (§56)

```
COMPLETE LOCAL FORMULA K_ell            : KERNEL-PROVED DEFINITION
COPRIMALITY MASK = gcd INDICATOR        : KERNEL-PROVED
PERIODICITY K_ell(s+ell) = K_ell(s)     : KERNEL-PROVED
COMPLETED OUTER d ∣ ell FIBRE           : KERNEL-PROVED
PRIME SPECIALISATION K_p = β(p)1_{p∣s}  : KERNEL-PROVED
CRT EXPANSION (disjoint prime pairs)    : KERNEL-PROVED
TERM COUNT 3^ω − 2^ω                    : KERNEL-PROVED
ω(ell) ≤ 4 FOR ODD ell ≤ 5000           : KERNEL-PROVED
≤ 65 CRT ATOMS PER ell                  : KERNEL-PROVED
SECOND d-FIBRE SUMMATION                : ILLEGAL DOUBLE COUNT (kernel-proved witness)
```

The complete local formula, for odd squarefree `ℓ` with `(ℓ, z) = 1`, is

    K_ℓ(s,z) = c_ℓ · 1_{(ℓ, z−s) = 1} · [ ∏_{p ∣ (ℓ,s)} (2 − p) − 1 ],
    c_ℓ      = μ(ℓ) β(ℓ) / φ(ℓ).

`outer_fibre_expansion` shows the bracket **already contains** the completed outer `d ∣ ℓ`
fibre: it is exactly `∑_{∅ ≠ A ⊆ p(ℓ,s)} ∏_{p ∈ A}(1−p)`.  Summing a second `d`-fibre on top
of it is therefore an **illegal double count**, witnessed by `second_dfibre_double_count`.

The CRT expansion `Kell_crt_expansion` writes `K_ℓ` as a finite sum over pairs `(A,B)` of
**disjoint** subsets of the prime factors of `ℓ` with `A ≠ ∅` — the subset form of "coprime
`a,b` with `ab ∣ ℓ`, `a > 1`".  Its term count is `3^ω(ℓ) − 2^ω(ℓ)`, and for odd `ℓ ≤ 5000`
one has `ω(ℓ) ≤ 4`, hence at most `3⁴ − 2⁴ = 65` atoms per `ℓ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §56.1  The local formula -/

/-- `λ_A = ∏_{p ∈ A} (1 − p)`, the CRT coefficient of the prime subset `A`. -/
def lambdaSub (A : Finset ℕ) : ℚ := ∏ p ∈ A, (1 - (p : ℚ))

/-- The normalising constant `c_ℓ = μ(ℓ) β(ℓ) / φ(ℓ)`. -/
def cEll (ell : ℕ) : ℚ :=
  ((ArithmeticFunction.moebius ell : ℤ) : ℚ) * beta ell / (Nat.totient ell : ℚ)

/-- The prime factors of `ℓ` dividing `x`; equivalently the prime factors of `gcd(ℓ,x)`. -/
def gcdFactors (ell : ℕ) (x : ℤ) : Finset ℕ := ell.primeFactors.filter (fun p => (p : ℤ) ∣ x)

/-- The coprimality mask `1_{(ℓ,x)=1}` in product form. -/
def coprimeMask (ell : ℕ) (x : ℤ) : ℚ :=
  ∏ p ∈ ell.primeFactors, (if (p : ℤ) ∣ x then (0 : ℚ) else 1)

/-- The complete local formula `K_ℓ(s,z)`. -/
def Kell (ell : ℕ) (s z : ℤ) : ℚ :=
  cEll ell * coprimeMask ell (z - s) * ((∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1)

/-- **`coprimeMask_eq_indicator`.**  `KERNEL-PROVED`.  The product mask is exactly the
coprimality indicator `1_{gcd(ℓ,x)=1}`. -/
theorem coprimeMask_eq_indicator {ell : ℕ} (hell : ell ≠ 0) (x : ℤ) :
    coprimeMask ell x = if Int.gcd (ell : ℤ) x = 1 then 1 else 0 := by
  rw [coprimeMask]
  by_cases hg : Int.gcd (ell : ℤ) x = 1
  · rw [if_pos hg]
    refine Finset.prod_eq_one fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpe : (p : ℤ) ∣ (ell : ℤ) := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hp)
    have hnd : ¬ ((p : ℤ) ∣ x) := by
      intro hx
      have hdvd : (p : ℕ) ∣ Int.gcd (ell : ℤ) x := Int.dvd_gcd hpe hx
      rw [hg] at hdvd
      exact hpp.one_lt.ne' (Nat.dvd_one.mp hdvd)
    simp [hnd]
  · rw [if_neg hg]
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := Int.gcd (ell : ℤ) x) hg
    have hpe : p ∣ ell := by
      have h1 : ((Int.gcd (ell : ℤ) x : ℕ) : ℤ) ∣ (ell : ℤ) := Int.gcd_dvd_left _ _
      have : (p : ℤ) ∣ (ell : ℤ) := dvd_trans (Int.natCast_dvd_natCast.2 hpd) h1
      exact_mod_cast this
    have hpx : (p : ℤ) ∣ x := dvd_trans (Int.natCast_dvd_natCast.2 hpd) (Int.gcd_dvd_right _ _)
    exact Finset.prod_eq_zero (i := p) (Nat.mem_primeFactors.2 ⟨hp, hpe, hell⟩) (by simp [hpx])

/-- **`gcdFactors_eq_primeFactors_gcd`.**  `KERNEL-PROVED`.  `gcdFactors ℓ x` really is the
set of prime factors of `gcd(ℓ,x)`. -/
theorem gcdFactors_eq_primeFactors_gcd {ell : ℕ} (hell : ell ≠ 0) (x : ℤ) :
    gcdFactors ell x = (Int.gcd (ell : ℤ) x).primeFactors := by
  ext p
  simp only [gcdFactors, Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hpe, -⟩, hpx⟩
    refine ⟨hp, Int.dvd_gcd (Int.natCast_dvd_natCast.2 hpe) hpx, ?_⟩
    intro h
    exact hell (by exact_mod_cast (Int.gcd_eq_zero_iff.mp h).1)
  · rintro ⟨hp, hpd, -⟩
    have h1 : ((Int.gcd (ell : ℤ) x : ℕ) : ℤ) ∣ (ell : ℤ) := Int.gcd_dvd_left _ _
    have hpe : p ∣ ell := by
      have : (p : ℤ) ∣ (ell : ℤ) := dvd_trans (Int.natCast_dvd_natCast.2 hpd) h1
      exact_mod_cast this
    exact ⟨⟨hp, hpe, hell⟩,
      dvd_trans (Int.natCast_dvd_natCast.2 hpd) (Int.gcd_dvd_right _ _)⟩

/-! ## §56.2  Periodicity -/

lemma dvd_shift_of_dvd_ell {ell p : ℕ} (hp : p ∈ ell.primeFactors) (x : ℤ) :
    ((p : ℤ) ∣ (x + ell) ↔ (p : ℤ) ∣ x) := by
  have hpe : (p : ℤ) ∣ (ell : ℤ) := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mem_primeFactors hp)
  constructor
  · intro h; simpa using dvd_sub h hpe
  · intro h; exact dvd_add h hpe

/-- **`Kell_periodic`.**  `KERNEL-PROVED`.  `K_ℓ(·, z)` has period `ℓ`. -/
theorem Kell_periodic (ell : ℕ) (s z : ℤ) : Kell ell (s + ell) z = Kell ell s z := by
  have hmask : coprimeMask ell (z - (s + ell)) = coprimeMask ell (z - s) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have h : ((p : ℤ) ∣ (z - (s + ell)) ↔ (p : ℤ) ∣ (z - s)) := by
      have := dvd_shift_of_dvd_ell hp (z - (s + ell))
      have heq : z - (s + ell) + ell = z - s := by ring
      rw [heq] at this
      exact this.symm
    by_cases hd : (p : ℤ) ∣ (z - s) <;> simp [h, hd]
  have hfac : gcdFactors ell (s + ell) = gcdFactors ell s := by
    refine Finset.filter_congr fun p hp => ?_
    simpa using dvd_shift_of_dvd_ell hp s
  rw [Kell, Kell, hmask, hfac]

/-! ## §56.3  The completed outer fibre -/

/-- **`outer_fibre_expansion`.**  `KERNEL-PROVED`.  The bracket of the local formula already
contains the completed outer `d ∣ ℓ` fibre:

    ∏_{p ∈ S} (2 − p) − 1 = ∑_{∅ ≠ A ⊆ S} ∏_{p ∈ A} (1 − p). -/
theorem outer_fibre_expansion (S : Finset ℕ) :
    (∏ p ∈ S, (2 - (p : ℚ))) - 1
      = ∑ A ∈ S.powerset.filter (fun A => A.Nonempty), lambdaSub A := by
  classical
  have hprod : (∏ p ∈ S, (2 - (p : ℚ))) = ∑ A ∈ S.powerset, lambdaSub A := by
    rw [show (∏ p ∈ S, (2 - (p : ℚ))) = ∏ p ∈ S, ((1 - (p : ℚ)) + 1) from
      Finset.prod_congr rfl (fun p _ => by ring), Finset.prod_add]
    exact Finset.sum_congr rfl fun A _ => by simp [lambdaSub]
  have hsplit : ∑ A ∈ S.powerset, lambdaSub A
      = ∑ A ∈ S.powerset.filter (fun A => A.Nonempty), lambdaSub A
        + ∑ A ∈ S.powerset.filter (fun A => ¬ A.Nonempty), lambdaSub A :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hempty : S.powerset.filter (fun A => ¬ A.Nonempty) = {∅} := by
    ext A
    simp [Finset.not_nonempty_iff_eq_empty, Finset.mem_filter, Finset.mem_powerset]
    intro h; exact h ▸ Finset.empty_subset S
  rw [hprod, hsplit, hempty]
  simp [lambdaSub]

/-! ## §56.4  The prime specialisation -/

lemma cEll_prime {p : ℕ} (hp : p.Prime) : cEll p = - beta p / ((p : ℚ) - 1) := by
  have hcast : ((Nat.totient p : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    norm_num
  rw [cEll, ArithmeticFunction.moebius_apply_prime hp, hcast]
  push_cast
  ring

/-- **`Kell_prime_specialisation`.**  `KERNEL-PROVED`.  For a prime `p` with `p ∤ z`,

    K_p(s,z) = β(p) · 1_{p ∣ s}. -/
theorem Kell_prime_specialisation {p : ℕ} (hp : p.Prime) {s z : ℤ} (hz : ¬ (p : ℤ) ∣ z) :
    Kell p s z = beta p * (if (p : ℤ) ∣ s then 1 else 0) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpf : (p : ℕ).primeFactors = {p} := hp.primeFactors
  by_cases hs : (p : ℤ) ∣ s
  · have hgf : gcdFactors p s = {p} := by
      rw [gcdFactors, hpf]
      simp [hs]
    have hzs : ¬ (p : ℤ) ∣ (z - s) := by
      intro h
      exact hz (by simpa using dvd_add h hs)
    have hmask : coprimeMask p (z - s) = 1 := by
      rw [coprimeMask, hpf]
      simp [hzs]
    have hp1 : ((p : ℚ) - 1) ≠ 0 := by
      have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
      intro h; linarith [sub_eq_zero.1 h]
    rw [Kell, hgf, hmask, cEll_prime hp, if_pos hs, Finset.prod_singleton]
    field_simp
    ring
  · have hgf : gcdFactors p s = ∅ := by
      rw [gcdFactors, hpf]
      simp [hs]
    rw [Kell, hgf, if_neg hs]
    simp

/-! ## §56.5  The CRT expansion -/

/-- The CRT atom attached to a pair of disjoint prime subsets. -/
def crtAtom (A B : Finset ℕ) (s z : ℤ) : ℚ :=
  lambdaSub A * (-1 : ℚ) ^ B.card *
    (if (∀ p ∈ A, (p : ℤ) ∣ s) ∧ (∀ p ∈ B, (p : ℤ) ∣ (z - s)) then 1 else 0)

/-- The CRT index set: pairs `(A,B)` of disjoint subsets of the prime factors of `ℓ` with
`A` nonempty (the subset form of "coprime `a,b`, `ab ∣ ℓ`, `a > 1`"). -/
def crtIndex (ell : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (ell.primeFactors.powerset ×ˢ ell.primeFactors.powerset).filter
    (fun q => Disjoint q.1 q.2 ∧ q.1.Nonempty)

/-- The full (not necessarily disjoint) index set. -/
def crtIndexFull (ell : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (ell.primeFactors.powerset ×ˢ ell.primeFactors.powerset).filter (fun q => q.1.Nonempty)

theorem crtIndex_subset (ell : ℕ) : crtIndex ell ⊆ crtIndexFull ell := by
  intro q hq
  rw [crtIndex, Finset.mem_filter] at hq
  rw [crtIndexFull, Finset.mem_filter]
  exact ⟨hq.1, hq.2.2⟩

/-- **`coprimeMask_expansion`.**  `KERNEL-PROVED`.  Möbius/CRT expansion of the coprimality
mask over subsets of the prime factors. -/
theorem coprimeMask_expansion (ell : ℕ) (x : ℤ) :
    coprimeMask ell x
      = ∑ B ∈ ell.primeFactors.powerset,
          (-1 : ℚ) ^ B.card * (if ∀ p ∈ B, (p : ℤ) ∣ x then 1 else 0) := by
  classical
  rw [coprimeMask,
    show (∏ p ∈ ell.primeFactors, (if (p : ℤ) ∣ x then (0 : ℚ) else 1))
        = ∏ p ∈ ell.primeFactors, ((-(if (p : ℤ) ∣ x then (1 : ℚ) else 0)) + 1) from
      Finset.prod_congr rfl (fun p _ => by by_cases h : (p : ℤ) ∣ x <;> simp [h]),
    Finset.prod_add]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [Finset.prod_const_one, mul_one, prod_neg, Finset.prod_boole]

/-- **`bracket_expansion`.**  `KERNEL-PROVED`.  The completed outer fibre, re-indexed over
nonempty subsets of the prime factors of `ℓ` with the divisibility mask on `s`. -/
theorem bracket_expansion (ell : ℕ) (s : ℤ) :
    (∏ p ∈ gcdFactors ell s, (2 - (p : ℚ))) - 1
      = ∑ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
          lambdaSub A * (if ∀ p ∈ A, (p : ℤ) ∣ s then 1 else 0) := by
  classical
  rw [outer_fibre_expansion (gcdFactors ell s)]
  have hcongr : ∀ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
      lambdaSub A * (if ∀ p ∈ A, (p : ℤ) ∣ s then (1 : ℚ) else 0)
        = if (∀ p ∈ A, (p : ℤ) ∣ s) then lambdaSub A else 0 := by
    intro A _
    by_cases h : ∀ p ∈ A, (p : ℤ) ∣ s <;> simp [h]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun A _ => rfl)
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, gcdFactors, Finset.subset_iff,
    Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun x hx => (h1 hx).1, h2⟩, fun p hp => (h1 hp).2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun x hx => ⟨h1 hx, h3 x hx⟩, h2⟩

/-- **`Kell_crt_expansion`.**  `KERNEL-PROVED`.  The CRT expansion of the complete local
formula: a finite sum over pairs `(A,B)` of **disjoint** prime subsets with `A ≠ ∅` — the
subset form of "coprime `a,b` with `ab ∣ ℓ` and `a > 1`". -/
theorem Kell_crt_expansion {ell : ℕ} {s z : ℤ}
    (hz : ∀ p ∈ ell.primeFactors, ¬ (p : ℤ) ∣ z) :
    Kell ell s z = cEll ell * ∑ q ∈ crtIndex ell, crtAtom q.1 q.2 s z := by
  classical
  rw [Kell, coprimeMask_expansion, bracket_expansion]
  have hswap :
      cEll ell *
          (∑ B ∈ ell.primeFactors.powerset,
            (-1 : ℚ) ^ B.card * (if ∀ p ∈ B, (p : ℤ) ∣ (z - s) then 1 else 0)) *
          (∑ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
            lambdaSub A * (if ∀ p ∈ A, (p : ℤ) ∣ s then 1 else 0))
        = cEll ell *
          ((∑ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
              lambdaSub A * (if ∀ p ∈ A, (p : ℤ) ∣ s then 1 else 0)) *
            ∑ B ∈ ell.primeFactors.powerset,
              (-1 : ℚ) ^ B.card * (if ∀ p ∈ B, (p : ℤ) ∣ (z - s) then 1 else 0)) := by
    ring
  rw [hswap, Finset.sum_mul_sum]
  congr 1
  have hatom : ∀ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
      ∀ B ∈ ell.primeFactors.powerset,
        (lambdaSub A * (if ∀ p ∈ A, (p : ℤ) ∣ s then (1 : ℚ) else 0)) *
          ((-1 : ℚ) ^ B.card * (if ∀ p ∈ B, (p : ℤ) ∣ (z - s) then 1 else 0))
          = crtAtom A B s z := by
    intro A _ B _
    rw [crtAtom]
    by_cases h1 : ∀ p ∈ A, (p : ℤ) ∣ s
    · by_cases h2 : ∀ p ∈ B, (p : ℤ) ∣ (z - s)
      · rw [if_pos h1, if_pos h2, if_pos (And.intro h1 h2)]; ring
      · rw [if_neg h2, if_neg (fun h : (∀ p ∈ A, (p : ℤ) ∣ s) ∧ (∀ p ∈ B, (p : ℤ) ∣ (z - s)) =>
          h2 h.2)]
        ring
    · rw [if_neg h1, if_neg (fun h : (∀ p ∈ A, (p : ℤ) ∣ s) ∧ (∀ p ∈ B, (p : ℤ) ∣ (z - s)) =>
        h1 h.1)]
      ring
  rw [Finset.sum_congr rfl (fun A hA => Finset.sum_congr rfl (fun B hB => hatom A hA B hB))]
  have hprod :
      ∑ A ∈ ell.primeFactors.powerset.filter (fun A => A.Nonempty),
          ∑ B ∈ ell.primeFactors.powerset, crtAtom A B s z
        = ∑ q ∈ crtIndexFull ell, crtAtom q.1 q.2 s z := by
    rw [← Finset.sum_product']
    refine Finset.sum_congr ?_ (fun q _ => rfl)
    ext q
    simp only [crtIndexFull, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    tauto
  rw [hprod]
  refine (Finset.sum_subset (crtIndex_subset ell) ?_).symm
  intro q hqfull hqnot
  rw [crtIndexFull, Finset.mem_filter] at hqfull
  rw [crtIndex, Finset.mem_filter] at hqnot
  have hnd : ¬ Disjoint q.1 q.2 := by
    intro hd
    exact hqnot ⟨hqfull.1, hd, hqfull.2⟩
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.1 hnd
  have hpP : p ∈ ell.primeFactors := by
    have := hqfull.1
    rw [Finset.mem_product, Finset.mem_powerset] at this
    exact this.1 hpA
  rw [crtAtom]
  have hcond : ¬ ((∀ r ∈ q.1, (r : ℤ) ∣ s) ∧ (∀ r ∈ q.2, (r : ℤ) ∣ (z - s))) := by
    rintro ⟨h1, h2⟩
    exact hz p hpP (by simpa using dvd_add (h2 p hpB) (h1 p hpA))
  simp [hcond]

/-! ## §56.6  Counting the CRT atoms -/

/-- **`disjoint_pairs_card`.**  `KERNEL-PROVED`.  The number of pairs of disjoint subsets of
a finite set of size `ω` is `3^ω`. -/
theorem disjoint_pairs_card (P : Finset ℕ) :
    ((P.powerset ×ˢ P.powerset).filter (fun q => Disjoint q.1 q.2)).card = 3 ^ P.card := by
  classical
  have hcard :
      ((P.powerset ×ˢ P.powerset).filter (fun q => Disjoint q.1 q.2)).card
        = ∑ A ∈ P.powerset, (P.powerset.filter (fun B => Disjoint A B)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun A _ => by rw [Finset.card_filter]
  have hfib : ∀ A ∈ P.powerset,
      (P.powerset.filter (fun B => Disjoint A B)) = (P \ A).powerset := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
    constructor
    · rintro ⟨hBP, hdisj⟩; exact ⟨hBP, hdisj.symm⟩
    · rintro ⟨hBP, hdisj⟩; exact ⟨hBP, hdisj.symm⟩
  rw [hcard, Finset.sum_congr rfl (fun A hA => by rw [hfib A hA])]
  have hpow : ∀ A ∈ P.powerset, ((P \ A).powerset).card = 2 ^ (P \ A).card := fun A _ => by
    rw [Finset.card_powerset]
  rw [Finset.sum_congr rfl hpow]
  have h3 : (3 : ℕ) ^ P.card = ∏ _p ∈ P, (1 + 2) := by
    rw [Finset.prod_const, Finset.card_eq_sum_ones]
  rw [h3, Finset.prod_add]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.prod_const_one, Finset.prod_const, one_mul]

/-- **`crtIndex_card`.**  `KERNEL-PROVED`.  The CRT term count is `3^ω − 2^ω`. -/
theorem crtIndex_card (ell : ℕ) :
    (crtIndex ell).card = 3 ^ ell.primeFactors.card - 2 ^ ell.primeFactors.card := by
  classical
  set P := ell.primeFactors with hP
  have hsplit :
      ((P.powerset ×ˢ P.powerset).filter (fun q => Disjoint q.1 q.2)).card
        = (crtIndex ell).card
          + (((P.powerset ×ˢ P.powerset).filter
              (fun q => Disjoint q.1 q.2 ∧ ¬ q.1.Nonempty)).card) := by
    rw [crtIndex, ← Finset.filter_filter, ← Finset.filter_filter,
      Finset.card_filter_add_card_filter_not (p := fun q => (q : Finset ℕ × Finset ℕ).1.Nonempty)]
  have hempty :
      ((P.powerset ×ˢ P.powerset).filter (fun q => Disjoint q.1 q.2 ∧ ¬ q.1.Nonempty)).card
        = 2 ^ P.card := by
    have hset :
        (P.powerset ×ˢ P.powerset).filter (fun q => Disjoint q.1 q.2 ∧ ¬ q.1.Nonempty)
          = {(∅ : Finset ℕ)} ×ˢ P.powerset := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_singleton, Finset.not_nonempty_iff_eq_empty]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h4⟩; exact ⟨h4, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨by rw [h1]; exact Finset.empty_subset _, h2⟩, ?_, h1⟩
        rw [h1]; exact disjoint_bot_left
    rw [hset, Finset.card_product, Finset.card_singleton, Finset.card_powerset, one_mul]
  rw [disjoint_pairs_card P] at hsplit
  omega

/-! ## §56.7  `ω(ℓ) ≤ 4` for odd `ℓ ≤ 5000` -/

/-- Lower bound for a product of `k` distinct odd numbers all `≥ m`. -/
theorem odd_prod_lower : ∀ (k m : ℕ) (S : Finset ℕ), S.card = k →
    (∀ x ∈ S, Odd x ∧ m ≤ x) → ∏ i ∈ Finset.range k, (m + 2 * i) ≤ ∏ x ∈ S, x := by
  intro k
  induction k with
  | zero =>
      intro m S hS _
      rw [Finset.card_eq_zero] at hS
      simp [hS]
  | succ k ih =>
      intro m S hcard hS
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x₀, hx₀, hmin⟩ := S.exists_min_image id hne
      have hcard' : (S.erase x₀).card = k := by
        rw [Finset.card_erase_of_mem hx₀, hcard]
        omega
      have hS' : ∀ x ∈ S.erase x₀, Odd x ∧ (m + 2) ≤ x := by
        intro x hx
        have hxS : x ∈ S := Finset.mem_of_mem_erase hx
        have hxne : x ≠ x₀ := Finset.ne_of_mem_erase hx
        have hge : x₀ ≤ x := hmin x hxS
        obtain ⟨a, ha⟩ := (hS x hxS).1
        obtain ⟨b, hb⟩ := (hS x₀ hx₀).1
        have hm := (hS x₀ hx₀).2
        exact ⟨⟨a, ha⟩, by omega⟩
      have hIH := ih (m + 2) (S.erase x₀) hcard' hS'
      have hreindex : ∏ i ∈ Finset.range (k + 1), (m + 2 * i)
          = (∏ i ∈ Finset.range k, ((m + 2) + 2 * i)) * m := by
        rw [Finset.prod_range_succ']
        congr 1
        exact Finset.prod_congr rfl fun i _ => by ring
      have hprod : ∏ x ∈ S, x = x₀ * ∏ x ∈ S.erase x₀, x := (Finset.mul_prod_erase S id hx₀).symm
      rw [hreindex, hprod, mul_comm x₀ _]
      exact Nat.mul_le_mul hIH (hS x₀ hx₀).2

/-- **`omega_le_four_of_odd_le_5000`.**  `KERNEL-PROVED`.  Every odd `ℓ ≤ 5000` has at most
four distinct prime factors (five distinct odd primes already multiply to at least
`3·5·7·9·11 = 10395 > 5000`). -/
theorem omega_le_four_of_odd_le_5000 {ell : ℕ} (hodd : Odd ell) (hle : ell ≤ 5000)
    (hpos : 0 < ell) : ell.primeFactors.card ≤ 4 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := ell.primeFactors) (n := 5)
    (by omega)
  have hSprop : ∀ x ∈ S, Odd x ∧ 3 ≤ x := by
    intro x hx
    have hxp : x ∈ ell.primeFactors := hSsub hx
    have hprime : x.Prime := Nat.prime_of_mem_primeFactors hxp
    have hdvd : x ∣ ell := Nat.dvd_of_mem_primeFactors hxp
    have hx2 : x ≠ 2 := by
      intro h
      rw [h] at hdvd
      have hmod := Nat.odd_iff.mp hodd
      omega
    have hodd' : Odd x := hprime.odd_of_ne_two hx2
    have : 3 ≤ x := by
      have := hprime.two_le
      omega
    exact ⟨hodd', this⟩
  have hbound := odd_prod_lower 5 3 S hScard hSprop
  have hval : ∏ i ∈ Finset.range 5, (3 + 2 * i) = 10395 := by decide
  have hdvd : (∏ x ∈ S, x) ∣ ∏ p ∈ ell.primeFactors, p :=
    Finset.prod_dvd_prod_of_subset _ _ _ hSsub
  have hdvd2 : (∏ p ∈ ell.primeFactors, p) ∣ ell := Nat.prod_primeFactors_dvd ell
  have hle2 : (∏ x ∈ S, x) ≤ ell := Nat.le_of_dvd hpos (hdvd.trans hdvd2)
  rw [hval] at hbound
  omega

/-- **`crt_atoms_le_65`.**  `KERNEL-PROVED`.  For odd `ℓ ≤ 5000` the CRT expansion has at
most `3⁴ − 2⁴ = 65` atoms. -/
theorem crt_atoms_le_65 {ell : ℕ} (hodd : Odd ell) (hle : ell ≤ 5000) (hpos : 0 < ell) :
    (crtIndex ell).card ≤ 65 := by
  have hω := omega_le_four_of_odd_le_5000 hodd hle hpos
  rw [crtIndex_card]
  have key : ∀ w : ℕ, w ≤ 4 → 3 ^ w - 2 ^ w ≤ 65 := by
    intro w hw
    interval_cases w <;> norm_num
  exact key _ hω

/-! ## §56.8  Firewall: the second `d`-fibre summation is an illegal double count -/

lemma beta_pos_of_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 0 < beta p := by
  rw [beta_prime hp h2]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  exact div_pos one_pos (by linarith)

/-- **`second_dfibre_double_count`.**  `KERNEL-PROVED`.  The complete local formula already
contains the outer `d ∣ ℓ` fibre (`outer_fibre_expansion`), so adding a **second** `d`-fibre
summation strictly changes the value: it is an illegal double count.  Witnessed at
`s = ℓ`, `z = ℓ + 1`, where the spurious second fibre contributes `∑_{p ∣ ℓ} β(p) > 0`. -/
theorem second_dfibre_double_count {ell : ℕ} (hodd : Odd ell)
    (hne : ell.primeFactors.Nonempty) :
    Kell ell (ell : ℤ) ((ell : ℤ) + 1)
        + ∑ p ∈ ell.primeFactors, Kell p (ell : ℤ) ((ell : ℤ) + 1)
      ≠ Kell ell (ell : ℤ) ((ell : ℤ) + 1) := by
  have hterm : ∀ p ∈ ell.primeFactors, Kell p (ell : ℤ) ((ell : ℤ) + 1) = beta p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvdn : p ∣ ell := Nat.dvd_of_mem_primeFactors hp
    have hdvd : (p : ℤ) ∣ (ell : ℤ) := Int.natCast_dvd_natCast.2 hdvdn
    have hz : ¬ (p : ℤ) ∣ ((ell : ℤ) + 1) := by
      intro h
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub h hdvd
        simpa using this
      have : p ∣ 1 := by exact_mod_cast h1
      exact hprime.one_lt.ne' (Nat.dvd_one.mp this)
    rw [Kell_prime_specialisation hprime hz, if_pos hdvd, mul_one]
  have hpos : 0 < ∑ p ∈ ell.primeFactors, beta p := by
    refine Finset.sum_pos (fun p hp => ?_) hne
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvdn : p ∣ ell := Nat.dvd_of_mem_primeFactors hp
    have h2 : p ≠ 2 := by
      intro h
      rw [h] at hdvdn
      have := Nat.odd_iff.mp hodd
      omega
    exact beta_pos_of_odd_prime hprime h2
  rw [Finset.sum_congr rfl hterm]
  intro hcon
  have hzero : ∑ p ∈ ell.primeFactors, beta p = 0 := by linarith [hcon]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

end Effectivity
end Erdos287
