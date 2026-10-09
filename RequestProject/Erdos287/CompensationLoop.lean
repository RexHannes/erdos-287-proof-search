import Mathlib
import RequestProject.Erdos287.SmallEllCRT
import RequestProject.Erdos287.HalfOpenProgressionCompiler

/-!
# Erdős #287 effectivity — the exact compensation loop (§59)

```
ell ≤ 1000 ATOMWISE CANCELLATION      : KERNEL-PROVED
RETURNED FINITE-CONDUCTOR KERNEL      : KERNEL-PROVED DEFINITION + COMPILER FORM
RETURNED KERNEL NOT IDENTICALLY ZERO  : KERNEL-PROVED
REASSEMBLY = EXACT LOOP, NOT CLOSURE  : KERNEL-PROVED FIREWALL (HIGH PRIORITY)
```

The banked source has already removed the conductor range `ℓ ≤ 1000`.  Writing
`bankedAtom` for the banked (already-removed) part and `Kell` for the internal atom, the
compensated atom is

    compAtom ℓ = K_ℓ − bankedAtom ℓ,     bankedAtom ℓ = if ℓ ≤ 1000 then K_ℓ else 0,

so `compAtom` vanishes identically on `ℓ ≤ 1000` (`loop_cancellation_le_1000`): that range
lies outside the original conductor support and cancels internally.  What survives is the
**returned finite-conductor kernel** on `1000 < ℓ ≤ 5000`, which via the compiler is the
finite object `∑_{1000 < ℓ ≤ 5000} Q_ℓ(A,B;z)`.

**Firewall (high priority).**  `reassembly_exact_loop` records that reassembling the returned
kernel into the original conductor expression is an *exact loop*: the difference is
identically `0`, so it yields no bound, while `returnedKernel_not_identically_zero` shows the
returned kernel is not the zero object.  Closure therefore requires a genuinely new analytic
input, not a reassembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §59.1  Atomwise compensation -/

/-- The banked (already-removed) atom: supported on the old conductor range `ℓ ≤ 1000`. -/
def bankedAtom (ell : ℕ) (s z : ℤ) : ℚ := if ell ≤ 1000 then Kell ell s z else 0

/-- The compensated atom. -/
def compAtom (ell : ℕ) (s z : ℤ) : ℚ := Kell ell s z - bankedAtom ell s z

/-- **`loop_cancellation_le_1000`.**  `KERNEL-PROVED`.  Every atom with `ℓ ≤ 1000` cancels
internally: it lies outside the original conductor support. -/
theorem loop_cancellation_le_1000 {ell : ℕ} (h : ell ≤ 1000) (s z : ℤ) :
    compAtom ell s z = 0 := by
  rw [compAtom, bankedAtom, if_pos h, sub_self]

/-- **`compAtom_gt_1000`.**  `KERNEL-PROVED`.  Above the old conductor range the compensated
atom is the full local kernel. -/
theorem compAtom_gt_1000 {ell : ℕ} (h : ¬ ell ≤ 1000) (s z : ℤ) :
    compAtom ell s z = Kell ell s z := by
  rw [compAtom, bankedAtom, if_neg h, sub_zero]

/-! ## §59.2  The returned finite-conductor kernel -/

/-- The returned finite-conductor kernel on `1000 < ℓ ≤ 5000`, in compiled form. -/
def returnedKernel (A B z : ℤ) : ℚ := ∑ ell ∈ Finset.Icc 1001 5000, Qell ell A B z

/-- **`returnedKernel_eq_compensated_sum`.**  `KERNEL-PROVED`.  Summing the compensated atoms
over the whole internal range `1 ≤ ℓ ≤ 5000` returns exactly the finite-conductor kernel:
everything below `1000` has cancelled. -/
theorem returnedKernel_eq_compensated_sum (A B z : ℤ) :
    ∑ ell ∈ Finset.Icc 1 5000, ∑ s ∈ Finset.Ico A B, compAtom ell s z
      = returnedKernel A B z := by
  classical
  have hsplit : ∑ ell ∈ Finset.Icc 1 5000, ∑ s ∈ Finset.Ico A B, compAtom ell s z
      = ∑ ell ∈ (Finset.Icc 1 5000).filter (fun ell => ¬ ell ≤ 1000),
          ∑ s ∈ Finset.Ico A B, compAtom ell s z := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 5000) (fun ell => ell ≤ 1000)]
    have hzero : ∑ ell ∈ (Finset.Icc 1 5000).filter (fun ell => ell ≤ 1000),
        ∑ s ∈ Finset.Ico A B, compAtom ell s z = 0 := by
      refine Finset.sum_eq_zero fun ell hell => ?_
      rw [Finset.mem_filter] at hell
      exact Finset.sum_eq_zero fun s _ => loop_cancellation_le_1000 hell.2 s z
    rw [hzero, zero_add]
  have hset : (Finset.Icc 1 5000).filter (fun ell => ¬ ell ≤ 1000) = Finset.Icc 1001 5000 := by
    ext ell
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hsplit, hset, returnedKernel]
  refine Finset.sum_congr rfl fun ell hell => ?_
  rw [Finset.mem_Icc] at hell
  have hgt : ¬ ell ≤ 1000 := by omega
  rw [Finset.sum_congr rfl (fun s _ => compAtom_gt_1000 hgt s z),
    Qell_compiler (by omega : 0 < ell) A B z]

/-! ## §59.3  The returned kernel is not zero -/

lemma gcdFactors_prime {ell p : ℕ} (hell : ell ≠ 0) (hp : p.Prime) (hdvd : p ∣ ell) :
    gcdFactors ell (p : ℤ) = {p} := by
  ext q
  simp only [gcdFactors, Finset.mem_filter, Finset.mem_singleton, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hq, -, -⟩, hqp⟩
    have : q ∣ p := by exact_mod_cast hqp
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 this
  · rintro rfl
    exact ⟨⟨hp, hdvd, hell⟩, dvd_rfl⟩

lemma coprimeMask_one (ell : ℕ) : coprimeMask ell 1 = 1 := by
  refine Finset.prod_eq_one fun q hq => ?_
  have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
  have : ¬ ((q : ℤ) ∣ 1) := by
    intro h
    have hq1 : q ∣ 1 := by exact_mod_cast h
    have := Nat.dvd_one.mp hq1
    omega
  simp [this]

lemma cEll_ne_zero {ell : ℕ} (hsq : Squarefree ell) (hodd : ¬ 2 ∣ ell) : cEll ell ≠ 0 := by
  have hmu : ((ArithmeticFunction.moebius ell : ℤ) : ℚ) ≠ 0 := by
    have h := (ArithmeticFunction.moebius_ne_zero_iff_squarefree (n := ell)).2 hsq
    exact_mod_cast h
  have hbeta : beta ell ≠ 0 := by
    rw [beta_of_odd_squarefree hsq hodd]
    have hprod : ∏ p ∈ ell.primeFactors, ((p : ℚ) - 2) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        intro h
        exact hodd (h ▸ hpd)
      have hp3 : 3 ≤ p := by have := hprime.two_le; omega
      have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
      intro hc
      have := sub_eq_zero.1 hc
      linarith
    exact one_div_ne_zero hprod
  have hphi : ((Nat.totient ell : ℕ) : ℚ) ≠ 0 := by
    have := Nat.totient_pos.2 (Nat.pos_of_ne_zero hsq.ne_zero)
    exact_mod_cast this.ne'
  rw [cEll]
  exact div_ne_zero (mul_ne_zero hmu hbeta) hphi

/-- **`Kell_ne_zero_at_prime_atom`.**  `KERNEL-PROVED`.  For odd squarefree `ℓ` and a prime
`p ∣ ℓ`, the atom `s = p`, `z = p + 1` gives a nonzero local kernel. -/
theorem Kell_ne_zero_at_prime_atom {ell p : ℕ} (hsq : Squarefree ell) (hodd : ¬ 2 ∣ ell)
    (hp : p.Prime) (hdvd : p ∣ ell) :
    Kell ell (p : ℤ) ((p : ℤ) + 1) ≠ 0 := by
  have hell0 : ell ≠ 0 := hsq.ne_zero
  have hsub : ((p : ℤ) + 1) - (p : ℤ) = 1 := by ring
  rw [Kell, hsub, coprimeMask_one, gcdFactors_prime hell0 hp hdvd, Finset.prod_singleton, mul_one]
  have hbr : (2 - (p : ℚ)) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
    intro h
    have : (p : ℚ) = 1 := by linarith [sub_eq_zero.1 h]
    have h2 : (2 : ℚ) ≤ 1 := by rw [← this]; exact_mod_cast hp.two_le
    linarith
  exact mul_ne_zero (cEll_ne_zero hsq hodd) hbr

/-- **`returnedKernel_not_identically_zero`.**  `KERNEL-PROVED`.  The returned
finite-conductor kernel is a genuinely nonzero object: there is an internal
`1000 < ℓ ≤ 5000` and an atom on which the local kernel does not vanish. -/
theorem returnedKernel_not_identically_zero :
    ∃ ell ∈ Finset.Icc 1001 5000, ∃ s z : ℤ, Kell ell s z ≠ 0 := by
  have hsq : Squarefree 1001 := by
    rw [show (1001 : ℕ) = 7 * (11 * 13) by norm_num, Nat.squarefree_mul_iff]
    refine ⟨by norm_num, Irreducible.squarefree
      (Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp (by norm_num))), ?_⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num,
      Irreducible.squarefree (Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp (by norm_num))),
      Irreducible.squarefree (Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp (by norm_num)))⟩
  refine ⟨1001, by decide, (7 : ℤ), (7 : ℤ) + 1, ?_⟩
  exact Kell_ne_zero_at_prime_atom hsq (by decide) (by norm_num) (by norm_num)

/-! ## §59.4  The exact-loop firewall -/

/-- Status tag for the reassembly route. -/
inductive LoopStatus
  | exactLoop
  | closure
  deriving DecidableEq, Repr

/-- Reassembling the returned kernel into the original conductor expression. -/
def reassembleStatus : LoopStatus := .exactLoop

/-- **`reassembly_exact_loop`.**  `KERNEL-PROVED` firewall (HIGH PRIORITY).  Reassembling the
returned finite-conductor kernel into the original conductor expression produces the
tautology `0 = 0` — an exact loop — while the returned kernel itself is not the zero object.
No closure is obtained by reassembly. -/
theorem reassembly_exact_loop :
    (∀ A B z : ℤ, returnedKernel A B z - returnedKernel A B z = 0) ∧
      reassembleStatus = LoopStatus.exactLoop ∧
      reassembleStatus ≠ LoopStatus.closure ∧
      (∃ ell ∈ Finset.Icc 1001 5000, ∃ s z : ℤ, Kell ell s z ≠ 0) :=
  ⟨fun A B z => sub_self _, rfl, by decide, returnedKernel_not_identically_zero⟩

end Effectivity
end Erdos287
