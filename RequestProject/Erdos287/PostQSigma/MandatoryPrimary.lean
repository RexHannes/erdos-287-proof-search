import RequestProject.Erdos287.PostQSigma.PrimaryCover

/-!
# Erdős #287 — post-`Q_Σ` bank, §7 (V56): mandatory primary layers

**Status: BANK (proved in Lean).**

* `Mandatory a M R p d :↔ 0 < κ_{p,d} ∧ κ_{p,d} = |S_{p,d}|`;
* `mandatory_subset_solution` — a mandatory layer lies inside every exact solution;
* `MAND a M R` — the union of all mandatory layers (`p ∣ W`, `1 ≤ d ≤ e_p`);
* `MAND_subset_solution`, `mandatory_adjacency_excludes` — two consecutive integers in `MAND`
  kill the source;
* `infeasible_excludes` — `κ_{p,d} = ∞` (empty repair set) kills the source (re-export).

No finite census is used.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

variable {a M : ℕ} {R : Finset ℕ}

/-- The layer `S_{p,d}` is **mandatory**: `0 < κ_{p,d} = |S_{p,d}|`. -/
def Mandatory (a M : ℕ) (R : Finset ℕ) (p d : ℕ) : Prop :=
  0 < kappa a M R p d ∧ kappa a M R p d = (S a M R p d).card

/-- **A mandatory layer is contained in every exact omission solution.** -/
theorem mandatory_subset_solution (ha : 0 < a) {p d : ℕ} (hp : p.Prime)
    (hd : d ≤ eW a M R p) (hm : Mandatory a M R p d) {E : Finset ℕ}
    (h : SourceSol a M R E) : S a M R p d ⊆ E := by
  have h1 := kappa_le_card_inter_S ha h hp hd
  rw [hm.2] at h1
  have heq : E ∩ S a M R p d = S a M R p d :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right h1
  intro n hn
  rw [← heq] at hn
  exact (Finset.mem_inter.1 hn).1

open Classical in
/-- `MAND(a, M)`: the union of all mandatory prime-depth layers. -/
noncomputable def MAND (a M : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (W a M R).primeFactors.biUnion (fun p =>
    ((Finset.Icc 1 (eW a M R p)).filter (fun d => Mandatory a M R p d)).biUnion
      (fun d => S a M R p d))

theorem mem_MAND {n : ℕ} : n ∈ MAND a M R ↔ ∃ p ∈ (W a M R).primeFactors,
    ∃ d, 1 ≤ d ∧ d ≤ eW a M R p ∧ Mandatory a M R p d ∧ n ∈ S a M R p d := by
  classical
  simp only [MAND, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨p, hp, d, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨p, hp, d, h1, h2, h3, h4⟩
  · rintro ⟨p, hp, d, h1, h2, h3, h4⟩; exact ⟨p, hp, d, ⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- `MAND ⊆ E` for every exact solution `E`. -/
theorem MAND_subset_solution (ha : 0 < a) {E : Finset ℕ} (h : SourceSol a M R E) :
    MAND a M R ⊆ E := by
  intro n hn
  obtain ⟨p, hp, d, -, hd, hm, hnS⟩ := mem_MAND.1 hn
  exact mandatory_subset_solution ha (Nat.prime_of_mem_primeFactors hp) hd hm h hnS

/-- **Mandatory adjacency exclusion**: `n, n+1 ∈ MAND` ⇒ no exact solution. -/
theorem mandatory_adjacency_excludes (ha : 0 < a) {n : ℕ} (hn : n ∈ MAND a M R)
    (hn1 : n + 1 ∈ MAND a M R) (E : Finset ℕ) : ¬ SourceSol a M R E := by
  intro h
  exact h.2.1 n (MAND_subset_solution ha h hn) (MAND_subset_solution ha h hn1)

/-- `κ_{p,d} = ∞` (no repair set at all) ⇒ no exact solution (re-export of the bank). -/
theorem infeasible_excludes (ha : 0 < a) {p d : ℕ} (hp : p.Prime) (hd : d ≤ eW a M R p)
    (hinf : RepairSizes a M R p d = ∅) (E : Finset ℕ) : ¬ SourceSol a M R E :=
  no_solution_of_infeasible ha hp hd hinf E

end Erdos287.PostQSigma
