import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V7: exact mixed-modulus interval lifting (kernel)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Pure finite arithmetic; every theorem of this module is kernel-proved.

All masses are measured in numerator units of one fixed final denominator `J`: a coordinate
`n ∈ T` carries the integer weight `w n` (in the application `w n = J / n`).  A *reachable* value
is a value `∑_{x ∈ S} w x` of an **actual Boolean subset** `S ⊆ T` — never merely a residue class.

* `ReachesLattice w T g A B` : every integer of the arithmetic progression `gℤ ∩ [A, B]` is the
  weight of some subset `S ⊆ T`.
* `interval_lift` : **exact mixed-modulus lifting.**  Old lattice step `g`, new step `g'` with
  `g' ∣ g` (`g` need not be a prime, `g/g'` need not be coprime to anything, and the same prime
  direction may be used repeatedly), a buffer `buf` disjoint from `T` which realizes *every*
  residue class mod `g` by an actual subset of weight in `[0, cap]`.  Then
  `ReachesLattice w (T ∪ buf) g' (A + cap) B`.
* `lift_interval_nonempty` : the overlap inequality `A + cap + g' ≤ B` makes the lifted interval
  contain a lattice point (so the lift is not vacuous).
* `chain_reaches`, `chainSupport_card_le`, `chain_mass_eq` : the exact recursion for successive
  lifts, with its support and mass bookkeeping.

**Terminology firewall.**  Failure of the overlap inequality means the *lifting certificate* is
not applicable; it is **not** an UNSAT statement about the source (`lift_failure_is_not_unsat`).
-/

namespace Erdos287
namespace ResearchBankV7
namespace IntervalLifting

open Finset

/-! ## 1.  Reachability of a lattice interval by actual Boolean subsets -/

/-- `ReachesLattice w T g A B`: every multiple of `g` in `[A, B]` is the exact weight of an actual
subset of `T`. -/
def ReachesLattice (w : ℕ → ℤ) (T : Finset ℕ) (g A B : ℤ) : Prop :=
  ∀ n : ℤ, g ∣ n → A ≤ n → n ≤ B → ∃ S ⊆ T, ∑ x ∈ S, w x = n

/-- Reachability is monotone in the ground set: enlarging the coordinate set never destroys a
certified interval (the witnessing subsets are unchanged). -/
theorem ReachesLattice.mono {w : ℕ → ℤ} {T T' : Finset ℕ} {g A B : ℤ}
    (h : ReachesLattice w T g A B) (hTT : T ⊆ T') : ReachesLattice w T' g A B := by
  intro n hg hA hB
  obtain ⟨S, hS, hsum⟩ := h n hg hA hB
  exact ⟨S, hS.trans hTT, hsum⟩

/-- Reachability is monotone in the interval. -/
theorem ReachesLattice.shrink {w : ℕ → ℤ} {T : Finset ℕ} {g A B A' B' : ℤ}
    (h : ReachesLattice w T g A B) (hA : A ≤ A') (hB : B' ≤ B) :
    ReachesLattice w T g A' B' :=
  fun n hg hA' hB' => h n hg (hA.trans hA') (hB'.trans hB)

/-! ## 2.  The exact mixed-modulus lifting theorem -/

/-- **Exact interval lifting (kernel).**

`T` already reaches the `g`-lattice interval `[A, B]`.  The buffer `buf` (disjoint from `T`)
realizes, by actual Boolean subsets, every residue class mod `g` with weight in `[0, cap]`.  Then
the union reaches the *finer* `g'`-lattice interval `[A + cap, B]`, for any `g' ∣ g`.

No coprimality is assumed: `g/g'` may share factors with `g'`, so repeated prime-power directions
are allowed. -/
theorem interval_lift {w : ℕ → ℤ} {T buf : Finset ℕ} {g g' A B cap : ℤ}
    (hdisj : Disjoint T buf)
    (hold : ReachesLattice w T g A B)
    (hbuf : ∀ r : ℤ, ∃ S ⊆ buf, (∑ x ∈ S, w x) ≡ r [ZMOD g] ∧
      0 ≤ ∑ x ∈ S, w x ∧ (∑ x ∈ S, w x) ≤ cap) :
    ReachesLattice w (T ∪ buf) g' (A + cap) B := by
  intro n _ hA hB
  obtain ⟨Sb, hSb, hres, hlo, hhi⟩ := hbuf n
  set v : ℤ := ∑ x ∈ Sb, w x with hv
  have hdvd : g ∣ n - v := Int.ModEq.dvd hres
  obtain ⟨So, hSo, hsum⟩ := hold (n - v) hdvd (by linarith) (by linarith)
  refine ⟨So ∪ Sb, Finset.union_subset_union hSo hSb, ?_⟩
  have hd : Disjoint So Sb := Finset.disjoint_of_subset_left hSo
    (Finset.disjoint_of_subset_right hSb hdisj)
  rw [Finset.sum_union hd, hsum, ← hv]
  ring

/-- **Overlap inequality ⇒ the lifted interval is not vacuous.**  If `0 < g'` and
`A + cap + g' ≤ B`, then the lifted `g'`-lattice interval contains a point. -/
theorem lift_interval_nonempty {g' A B cap : ℤ} (hg' : 0 < g') (hover : A + cap + g' ≤ B) :
    ∃ n : ℤ, g' ∣ n ∧ A + cap ≤ n ∧ n ≤ B := by
  refine ⟨g' * ((A + cap) / g' + 1), ⟨_, rfl⟩, ?_, ?_⟩
  · have h := Int.mul_ediv_add_emod (A + cap) g'
    have hlt : (A + cap) % g' < g' := Int.emod_lt_of_pos _ hg'
    nlinarith [h, hlt]
  · have h := Int.mul_ediv_add_emod (A + cap) g'
    have hnn : 0 ≤ (A + cap) % g' := Int.emod_nonneg _ (ne_of_gt hg')
    nlinarith [h, hnn, hover]

/-! ## 3.  The exact recursion for successive lifts -/

/-- One lifting stage: a buffer, the new (finer) lattice step, and the buffer's weight cap. -/
structure Stage where
  /-- The buffer coordinates of this stage. -/
  buf : Finset ℕ
  /-- The new lattice step after this stage. -/
  gNew : ℤ
  /-- The cap on the buffer weight used at this stage. -/
  cap : ℤ

/-- The support after running a chain of stages. -/
def chainSupport (T : Finset ℕ) : List Stage → Finset ℕ
  | [] => T
  | st :: rest => chainSupport (T ∪ st.buf) rest

/-- The lattice step after running a chain of stages. -/
def chainG (g : ℤ) : List Stage → ℤ
  | [] => g
  | st :: rest => chainG st.gNew rest

/-- The lower endpoint after running a chain of stages (each stage costs its cap). -/
def chainLo (A : ℤ) : List Stage → ℤ
  | [] => A
  | st :: rest => chainLo (A + st.cap) rest

/-- Validity of a chain of stages over the ground set `T` at lattice step `g`. -/
def ChainValid (w : ℕ → ℤ) (T : Finset ℕ) (g : ℤ) : List Stage → Prop
  | [] => True
  | st :: rest =>
      Disjoint T st.buf ∧
      (∀ r : ℤ, ∃ S ⊆ st.buf, (∑ x ∈ S, w x) ≡ r [ZMOD g] ∧
        0 ≤ ∑ x ∈ S, w x ∧ (∑ x ∈ S, w x) ≤ st.cap) ∧
      ChainValid w (T ∪ st.buf) st.gNew rest

/-- **Exact recursion for successive lifts (kernel).**  A valid chain of lifting stages transports
a certified lattice interval through all stages, paying one cap per stage at the lower endpoint. -/
theorem chain_reaches {w : ℕ → ℤ} {B : ℤ} :
    ∀ (L : List Stage) (T : Finset ℕ) (g A : ℤ),
      ReachesLattice w T g A B → ChainValid w T g L →
      ReachesLattice w (chainSupport T L) (chainG g L) (chainLo A L) B := by
  intro L
  induction L with
  | nil => intro T g A h _; simpa [chainSupport, chainG, chainLo] using h
  | cons st rest ih =>
      intro T g A h hvalid
      obtain ⟨hdisj, hbuf, hrest⟩ := hvalid
      have hstep : ReachesLattice w (T ∪ st.buf) st.gNew (A + st.cap) B :=
        interval_lift hdisj h hbuf
      simpa [chainSupport, chainG, chainLo] using ih (T ∪ st.buf) st.gNew (A + st.cap) hstep hrest

/-- The support of a chain is the starter together with all buffers: explicit cardinality
bound. -/
theorem chainSupport_card_le :
    ∀ (L : List Stage) (T : Finset ℕ),
      (chainSupport T L).card ≤ T.card + (L.map (fun st => st.buf.card)).sum := by
  intro L
  induction L with
  | nil => intro T; simp [chainSupport]
  | cons st rest ih =>
      intro T
      have h1 := ih (T ∪ st.buf)
      have h2 : (T ∪ st.buf).card ≤ T.card + st.buf.card := Finset.card_union_le _ _
      simp only [chainSupport, List.map_cons, List.sum_cons]
      omega

/-- Every coordinate of the chain support is either a starter coordinate or lies in one of the
buffers. -/
theorem subset_chainSupport : ∀ (L : List Stage) (T : Finset ℕ), T ⊆ chainSupport T L := by
  intro L
  induction L with
  | nil => intro T; simp [chainSupport]
  | cons st rest ih =>
      intro T
      exact (Finset.subset_union_left).trans (ih (T ∪ st.buf))

/-- **Exact mass bookkeeping.**  Under chain validity all buffers are disjoint from the running
support, so the total mass of the chain support is exactly the starter mass plus the buffer
masses. -/
theorem chain_mass_eq {w : ℕ → ℤ} (f : ℕ → ℚ) :
    ∀ (L : List Stage) (T : Finset ℕ) (g : ℤ), ChainValid w T g L →
      ∑ x ∈ chainSupport T L, f x
        = ∑ x ∈ T, f x + (L.map (fun st => ∑ x ∈ st.buf, f x)).sum := by
  intro L
  induction L with
  | nil => intro T g _; simp [chainSupport]
  | cons st rest ih =>
      intro T g hvalid
      obtain ⟨hdisj, _, hrest⟩ := hvalid
      have h1 := ih (T ∪ st.buf) st.gNew hrest
      have h2 : ∑ x ∈ T ∪ st.buf, f x = ∑ x ∈ T, f x + ∑ x ∈ st.buf, f x :=
        Finset.sum_union hdisj
      simp only [chainSupport, List.map_cons, List.sum_cons]
      rw [h1, h2]
      ring

/-! ## 4.  Terminology firewall -/

/-- **Firewall.**  Non-applicability of a lifting certificate (a violated overlap inequality) is
*not* a statement that the source is unsatisfiable: a certificate may fail while the underlying
reachability statement is true.  Here the interval `[A + cap, B]` is empty as a lattice interval
because `B < A + cap`, yet the ground set does reach the value `0`. -/
theorem lift_failure_is_not_unsat :
    ∃ (w : ℕ → ℤ) (T : Finset ℕ) (g A B cap : ℤ),
      B < A + cap ∧ (∃ S ⊆ T, ∑ x ∈ S, w x = (0 : ℤ)) ∧ ReachesLattice w T g A B := by
  refine ⟨fun _ => 0, ∅, 1, 1, 0, 5, by norm_num, ⟨∅, by simp, by simp⟩, ?_⟩
  intro n _ hA hB
  exact absurd (hA.trans hB) (by norm_num)

end IntervalLifting
end ResearchBankV7
end Erdos287
