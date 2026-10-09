import RequestProject.Erdos287.PostQSigma.MandatoryDeep
import RequestProject.Erdos287.PostQSigma.MandatoryPrimary

/-!
# Erdős #287 — post-`Q_Σ` bank, §11 (V57): `MAND = MAND1 ∪ Ddeep`

**Status: BANK (proved in Lean)** for the decomposition and the localisation of the deep part;
the cardinality bound `|Ddeep| ≤ 5` is **not** formalised (PAPER-LEVEL; see the report).

* `MAND1 a M` — union of the mandatory first-digit (`d = 1`) layers;
* `Ddeep a M = MAND \ MAND1` — the additional deep coordinates;
* `mandatory_eq_first_digit_union_deep_exception` — `MAND = MAND1 ∪ Ddeep`;
* `Ddeep_disjoint` — `Ddeep ∩ MAND1 = ∅`;
* `Ddeep_localised` — (for `a ≥ 1`, `H(a,M) ≥ 1`) every element of `Ddeep` lies in a mandatory
  layer `S_{p,d}` with `(p,d) ∈ {(2,2),(2,3),(3,2),(5,2)}` (by `deep_mandatory_classification`);
* `Ddeep_prime_support` — consequently only the primes `2, 3, 5` contribute deep coordinates.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ}

open Classical in
/-- The first-digit mandatory union `MAND1`. -/
noncomputable def MAND1 (a M : ℕ) : Finset ℕ :=
  ((W a M ∅).primeFactors.filter (fun p => 1 ≤ eW a M ∅ p ∧ Mandatory a M ∅ p 1)).biUnion
    (fun p => S a M ∅ p 1)

/-- The deep exceptional part `Ddeep = MAND \ MAND1`. -/
noncomputable def Ddeep (a M : ℕ) : Finset ℕ := MAND a M ∅ \ MAND1 a M

theorem mem_MAND1 {n : ℕ} : n ∈ MAND1 a M ↔ ∃ p ∈ (W a M ∅).primeFactors,
    1 ≤ eW a M ∅ p ∧ Mandatory a M ∅ p 1 ∧ n ∈ S a M ∅ p 1 := by
  classical
  simp only [MAND1, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, h1, h2⟩, hn⟩; exact ⟨p, hp, h1, h2, hn⟩
  · rintro ⟨p, hp, h1, h2, hn⟩; exact ⟨p, ⟨hp, h1, h2⟩, hn⟩

theorem MAND1_subset_MAND : MAND1 a M ⊆ MAND a M ∅ := by
  intro n hn
  obtain ⟨p, hp, h1, h2, hnS⟩ := mem_MAND1.1 hn
  exact mem_MAND.2 ⟨p, hp, 1, le_rfl, h1, h2, hnS⟩

/-- **`MAND = MAND1 ∪ Ddeep`.** -/
theorem mandatory_eq_first_digit_union_deep_exception :
    MAND a M ∅ = MAND1 a M ∪ Ddeep a M := by
  rw [Ddeep, Finset.union_sdiff_of_subset MAND1_subset_MAND]

/-- **`Ddeep ∩ MAND1 = ∅`.** -/
theorem Ddeep_disjoint : Disjoint (Ddeep a M) (MAND1 a M) := Finset.sdiff_disjoint

/-- **Localisation of the deep part** on the harmonic domain. -/
theorem Ddeep_localised (ha : 0 < a) (hH : 1 ≤ Hm a M) {n : ℕ} (hn : n ∈ Ddeep a M) :
    ∃ p d, (p, d) ∈ deepExceptions ∧ Mandatory a M ∅ p d ∧ n ∈ S a M ∅ p d := by
  obtain ⟨hnM, hn1⟩ := Finset.mem_sdiff.1 hn
  obtain ⟨p, hp, d, hd1, hde, hm, hnS⟩ := mem_MAND.1 hnM
  rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
  · exact absurd (mem_MAND1.2 ⟨p, hp, hde, hm, hnS⟩) hn1
  · exact ⟨p, d, deep_mandatory_classification ha hH (Nat.prime_of_mem_primeFactors hp) hd2
      hde hm, hm, hnS⟩

/-- Only the primes `2, 3, 5` contribute deep coordinates. -/
theorem Ddeep_prime_support (ha : 0 < a) (hH : 1 ≤ Hm a M) {n : ℕ} (hn : n ∈ Ddeep a M) :
    ∃ p ∈ ({2, 3, 5} : Finset ℕ), ∃ d, 2 ≤ d ∧ d ≤ 3 ∧ Mandatory a M ∅ p d ∧
      n ∈ S a M ∅ p d := by
  obtain ⟨p, d, hpd, hm, hnS⟩ := Ddeep_localised ha hH hn
  simp only [deepExceptions, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpd
  rcases hpd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, by simp, _, by norm_num, by norm_num, hm, hnS⟩

end Erdos287.PostQSigma
