import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV9.GcdClique

/-!
# Erdős #287 — Research Bank V15 §B5: the moving CRT residue

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For the fixed tuple `a` and a divisor configuration with coordinate moduli
`m_i = lcm(d_i, e_i)`, the sieve condition is the congruence system

    m_i ∣ a_i t + 1     for all i                                    (`Solves a m t`).

Finite CRT algebra (kernel-proved):
* `collision_prime_dvd_diff` — a prime dividing two coordinate moduli of a solvable system divides
  `a_j − a_i` (shared primes are only possible at collisions of the tuple);
* `solves_periodic`, `solves_mod` — solutions are periodic modulo `L = lcm(m_i)`;
* `solves_unique_mod` — with `(a_i, m_i) = 1` two solutions agree modulo `L`;
* `solves_of_compatible` — **CRT consistency**: single-coordinate solutions `r_i` that are pairwise
  compatible (`gcd(m_i, m_j) ∣ r_i − r_j`) glue to a common solution (via the V9 general CRT);
* `crtResidue` — the actual (moving) residue: the least solution, which lies in `[0, L)`
  (`crtResidue_spec`); `residue_moves_with_tuple` — it depends on the tuple (root-dependent).

The analytic uniformity of Bombieri–Vinogradov over reduced residue classes is **not** used
here; it enters only through `BombieriVinogradovProvider.OrdinaryBVProvider`.
-/

namespace Erdos287
namespace ResearchBankV15
namespace CRTResidues

/-- The congruence system `m_i ∣ a_i t + 1`. -/
def Solves {K : ℕ} (a m : Fin K → ℕ) (t : ℕ) : Prop := ∀ i, m i ∣ a i * t + 1

/-- `L = lcm_i m_i`. -/
def Lmod {K : ℕ} (m : Fin K → ℕ) : ℕ := Finset.univ.lcm m

theorem dvd_Lmod {K : ℕ} (m : Fin K → ℕ) (i : Fin K) : m i ∣ Lmod m :=
  Finset.dvd_lcm (Finset.mem_univ i)

/-- **Collision lemma.** -/
theorem collision_prime_dvd_diff {K : ℕ} {a m : Fin K → ℕ} {t : ℕ} (h : Solves a m t)
    {p : ℕ} {i j : Fin K} (hi : p ∣ m i) (hj : p ∣ m j) : (p : ℤ) ∣ (a j : ℤ) - a i := by
  have h1 : (p : ℤ) ∣ (a i : ℤ) * t + 1 := by exact_mod_cast hi.trans (h i)
  have h2 : (p : ℤ) ∣ (a j : ℤ) * t + 1 := by exact_mod_cast hj.trans (h j)
  have := dvd_sub (dvd_mul_of_dvd_right h1 (a j : ℤ)) (dvd_mul_of_dvd_right h2 (a i : ℤ))
  rwa [show (a j : ℤ) * ((a i : ℤ) * t + 1) - (a i : ℤ) * ((a j : ℤ) * t + 1) =
    (a j : ℤ) - a i by ring] at this

/-- Periodicity. -/
theorem solves_periodic {K : ℕ} {a m : Fin K → ℕ} {t : ℕ} (h : Solves a m t) (k : ℕ) :
    Solves a m (t + k * Lmod m) := by
  intro i
  have : a i * (t + k * Lmod m) + 1 = (a i * t + 1) + a i * k * Lmod m := by ring
  rw [this]
  exact dvd_add (h i) (Dvd.dvd.mul_left (dvd_Lmod m i) _)

/-- Reduction modulo `L`. -/
theorem solves_mod {K : ℕ} {a m : Fin K → ℕ} {t : ℕ} (h : Solves a m t) :
    Solves a m (t % Lmod m) := by
  intro i
  have ht := Nat.mod_add_div t (Lmod m)
  have key := h i
  rw [← ht] at key
  have : a i * (t % Lmod m + Lmod m * (t / Lmod m)) + 1 =
      (a i * (t % Lmod m) + 1) + a i * (t / Lmod m) * Lmod m := by ring
  rw [this] at key
  exact (Nat.dvd_add_left (Dvd.dvd.mul_left (dvd_Lmod m i) _)).1 key

/-- **Uniqueness modulo `L`** under `(a_i, m_i) = 1`. -/
theorem solves_unique_mod {K : ℕ} {a m : Fin K → ℕ} {t t' : ℕ} (h : Solves a m t)
    (h' : Solves a m t') (hcop : ∀ i, Nat.Coprime (a i) (m i)) :
    ((Lmod m : ℕ) : ℤ) ∣ (t : ℤ) - t' := by
  have hi : ∀ i, m i ∣ ((t : ℤ) - t').natAbs := by
    intro i
    have h1 : (m i : ℤ) ∣ (a i : ℤ) * t + 1 := by exact_mod_cast h i
    have h2 : (m i : ℤ) ∣ (a i : ℤ) * t' + 1 := by exact_mod_cast h' i
    have h3 : (m i : ℤ) ∣ (a i : ℤ) * ((t : ℤ) - t') := by
      have := dvd_sub h1 h2
      rwa [show (a i : ℤ) * t + 1 - ((a i : ℤ) * t' + 1) = (a i : ℤ) * ((t : ℤ) - t') by ring]
        at this
    have hc : IsCoprime (m i : ℤ) (a i : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.2 (by rw [Int.gcd_natCast_natCast]; exact (hcop i).symm)
    exact Int.natCast_dvd.1 (hc.dvd_of_dvd_mul_left h3)
  exact Int.natCast_dvd.2 (Finset.lcm_dvd fun i _ => hi i)

/-- **CRT consistency**: pairwise-compatible single-coordinate solutions glue. -/
theorem solves_of_compatible {K : ℕ} {a m : Fin K → ℕ} (hm : ∀ i, m i ≠ 0) (r : Fin K → ℕ)
    (hr : ∀ i, m i ∣ a i * r i + 1)
    (hc : ∀ i j, ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ (r i : ℤ) - r j) :
    ∃ t, Solves a m t := by
  set l : List (ℤ × ℕ) := (Finset.univ : Finset (Fin K)).toList.map fun i => ((r i : ℤ), m i)
    with hl
  have hmem : ∀ q ∈ l, ∃ i, q = ((r i : ℤ), m i) := by
    intro q hq
    simp only [hl, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hq
    obtain ⟨i, rfl⟩ := hq
    exact ⟨i, rfl⟩
  obtain ⟨x, hx0, hx⟩ := ResearchBankV9.GcdClique.crt_exists_ge l
    (fun q hq => by obtain ⟨i, rfl⟩ := hmem q hq; exact hm i)
    (fun q hq q' hq' => by
      obtain ⟨i, rfl⟩ := hmem q hq; obtain ⟨j, rfl⟩ := hmem q' hq'; exact hc i j) 0
  refine ⟨x.toNat, fun i => ?_⟩
  have hq : ((r i : ℤ), m i) ∈ l := by
    simp only [hl, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have h1 : (m i : ℤ) ∣ x - r i := hx _ hq
  have h2 : (m i : ℤ) ∣ (a i : ℤ) * r i + 1 := by exact_mod_cast hr i
  have h3 : (m i : ℤ) ∣ (a i : ℤ) * x + 1 := by
    have := dvd_add h2 (dvd_mul_of_dvd_right h1 (a i : ℤ))
    rwa [show (a i : ℤ) * r i + 1 + (a i : ℤ) * (x - r i) = (a i : ℤ) * x + 1 by ring] at this
  have hxt : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0
  have : (m i : ℤ) ∣ ((a i * x.toNat + 1 : ℕ) : ℤ) := by push_cast; rw [hxt]; exact h3
  exact_mod_cast this

open Classical in
/-- **The moving CRT residue**: the least solution of the system (if any). -/
noncomputable def crtResidue {K : ℕ} (a m : Fin K → ℕ) : Option ℕ :=
  if h : ∃ t, Solves a m t then some (Nat.find h) else none

theorem crtResidue_spec {K : ℕ} {a m : Fin K → ℕ} (hL : 0 < Lmod m) {r : ℕ}
    (h : crtResidue a m = some r) : Solves a m r ∧ r < Lmod m := by
  classical
  unfold crtResidue at h
  split_ifs at h with hex
  · cases h
    refine ⟨Nat.find_spec hex, ?_⟩
    obtain ⟨t, ht⟩ := hex
    have h1 : Nat.find ⟨t, ht⟩ ≤ t % Lmod m := Nat.find_min' _ (solves_mod ht)
    exact lt_of_le_of_lt h1 (Nat.mod_lt _ hL)

theorem crtResidue_isSome {K : ℕ} {a m : Fin K → ℕ} {t : ℕ} (h : Solves a m t) :
    (crtResidue a m).isSome := by
  classical
  unfold crtResidue; rw [dif_pos ⟨t, h⟩]; rfl

/-- **The residue moves with the tuple** (root-dependent): for `m = 5`, `t = 4` solves the
system for `a = 1` but not for `a = 2`. -/
theorem residue_moves_with_tuple :
    Solves (K := 1) ![1] ![5] 4 ∧ ¬ Solves (K := 1) ![2] ![5] 4 := by
  unfold Solves; decide

end CRTResidues
end ResearchBankV15
end Erdos287
