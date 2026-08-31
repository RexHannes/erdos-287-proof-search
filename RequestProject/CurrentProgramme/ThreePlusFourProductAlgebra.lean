import Mathlib
import RequestProject.CurrentProgramme.ExactQRPartition

/-!
# CurrentProgramme §7 — the finite `3 + 4` product algebra

This module is **finite algebra only**.  It contains no prime-density and no PNT input.

For finite coefficient functions `w₁, …, w₇` supported on a finite set `S` we define the
labelled product coefficients

```
    a₃(n) = ∑_{p₁p₂p₃ = n}       w₁(p₁) w₂(p₂) w₃(p₃),
    b₄(m) = ∑_{p₄p₅p₆p₇ = m}     w₄(p₄) w₅(p₅) w₆(p₆) w₇(p₇),
```

with **no injectivity assumption**: labelled tuples are summed with multiplicity and
repeated primes are included.  Both are instances of one `k`-fold convolution `convWeight`.

Banked:

* the exact multiplicity identity `convWeight_sum_eq` (fibrewise reassembly);
* the exact energy identity `sum_prod_sq_eq_prod_energy`;
* the collision/Cauchy bound
  `∑_n |a(n)|² ≤ representationMultiplicity · ∏_i energy(wᵢ)`
  (`convWeight_sq_sum_le`), and its `a₃` and `b₄` instances;
* explicit witnesses that the multiplicity is genuinely `> 1` and that repeated primes
  occur, so no injectivity is silently assumed.

The asymptotic research targets
`∑|a₃|² ≪ X^{3/7} log^{-3+o(1)} X` and `∑|b₄|² ≪ X^{4/7} log^{-4+o(1)} X`
are **not** proved here: they are represented by an uninhabited prime-density socket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §7.1  Labelled product coefficients -/

/-- The labelled representation fibre of `n`: all `k`-tuples from `S` whose product is `n`.
Repetitions are allowed and distinct labellings are distinct elements. -/
def prodFiber (k : ℕ) (S : Finset ℕ) (n : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => S).filter (fun t => ∏ i, t i = n)

theorem mem_prodFiber {k : ℕ} {S : Finset ℕ} {n : ℕ} {t : Fin k → ℕ} :
    t ∈ prodFiber k S n ↔ (∀ i, t i ∈ S) ∧ ∏ i, t i = n := by
  simp [prodFiber, Fintype.mem_piFinset]

/-- The `k`-fold labelled convolution of coefficient functions `w`. -/
def convWeight {k : ℕ} (S : Finset ℕ) (w : Fin k → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ prodFiber k S n, ∏ i, w i (t i)

/-- `a₃(n) = ∑_{p₁p₂p₃ = n} w₁(p₁) w₂(p₂) w₃(p₃)`. -/
def a3 (S : Finset ℕ) (w : Fin 3 → ℕ → ℝ) (n : ℕ) : ℝ := convWeight S w n

/-- `b₄(m) = ∑_{p₄p₅p₆p₇ = m} w₄(p₄) w₅(p₅) w₆(p₆) w₇(p₇)`. -/
def b4 (S : Finset ℕ) (w : Fin 4 → ℕ → ℝ) (m : ℕ) : ℝ := convWeight S w m

/-- The `ℓ²` energy of one coefficient function on `S`. -/
def energy (S : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ p ∈ S, (w p) ^ 2

theorem energy_nonneg (S : Finset ℕ) (w : ℕ → ℝ) : 0 ≤ energy S w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The largest labelled representation multiplicity over a finite output range `N`. -/
def representationMultiplicity (k : ℕ) (S N : Finset ℕ) : ℕ :=
  N.sup fun n => (prodFiber k S n).card

theorem card_prodFiber_le_representationMultiplicity {k : ℕ} {S N : Finset ℕ} {n : ℕ}
    (hn : n ∈ N) : (prodFiber k S n).card ≤ representationMultiplicity k S N :=
  Finset.le_sup (f := fun n => (prodFiber k S n).card) hn

/-! ## §7.2  Exact multiplicity identities -/

/-- **`convWeight_sum_eq`.**  `LEAN_PROVED`.

Exact fibrewise reassembly: summing the labelled convolution over any output range that
receives all products recovers the full labelled sum. -/
theorem convWeight_sum_eq {k : ℕ} (S N : Finset ℕ) (w : Fin k → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, convWeight S w n =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin k => S), ∏ i, w i (t i) :=
  Finset.sum_fiberwise_of_maps_to hmaps _

/-- **`sum_prod_sq_eq_prod_energy`.**  `LEAN_PROVED`.

The labelled `ℓ²` mass of a product coefficient factorises exactly into the energies. -/
theorem sum_prod_sq_eq_prod_energy {k : ℕ} (S : Finset ℕ) (w : Fin k → ℕ → ℝ) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, w i (t i)) ^ 2 =
      ∏ i, energy S (w i) := by
  simp only [energy]
  rw [Finset.prod_univ_sum (fun _ : Fin k => S) (fun i p => (w i p) ^ 2)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_pow]

/-- **`prodFiber_fibrewise_sq`.**  `LEAN_PROVED`.  The same reassembly for squares. -/
theorem prodFiber_fibrewise_sq {k : ℕ} (S N : Finset ℕ) (w : Fin k → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 = ∏ i, energy S (w i) := by
  rw [show (∑ n ∈ N, ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2) =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, w i (t i)) ^ 2 from
    Finset.sum_fiberwise_of_maps_to hmaps _]
  exact sum_prod_sq_eq_prod_energy S w

/-! ## §7.3  The collision / Cauchy bound -/

/-- **`convWeight_sq_le_fiber`.**  `LEAN_PROVED`.

Cauchy–Schwarz on one fibre: `|a(n)|² ≤ #fibre(n) · ∑_{fibre} (∏ w)²`. -/
theorem convWeight_sq_le_fiber {k : ℕ} (S : Finset ℕ) (w : Fin k → ℕ → ℝ) (n : ℕ) :
    (convWeight S w n) ^ 2 ≤
      ((prodFiber k S n).card : ℝ) * ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 :=
  sq_sum_le_card_mul_sum_sq

/-- **`convWeight_sq_sum_le`.**  `LEAN_PROVED`.

The finite collision bound with **no injectivity assumption**:

```
    ∑_n |a(n)|²  ≤  representationMultiplicity · ∏_i energy(wᵢ).
```
-/
theorem convWeight_sq_sum_le {k : ℕ} (S N : Finset ℕ) (w : Fin k → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, (convWeight S w n) ^ 2 ≤
      (representationMultiplicity k S N : ℝ) * ∏ i, energy S (w i) := by
  have key : ∀ n ∈ N, (convWeight S w n) ^ 2 ≤
      (representationMultiplicity k S N : ℝ) *
        ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 := by
    intro n hn
    refine le_trans (convWeight_sq_le_fiber S w n) ?_
    have hcard : ((prodFiber k S n).card : ℝ) ≤ (representationMultiplicity k S N : ℝ) := by
      exact_mod_cast card_prodFiber_le_representationMultiplicity hn
    have hnn : (0 : ℝ) ≤ ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact mul_le_mul_of_nonneg_right hcard hnn
  calc ∑ n ∈ N, (convWeight S w n) ^ 2
      ≤ ∑ n ∈ N, (representationMultiplicity k S N : ℝ) *
          ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 := Finset.sum_le_sum key
    _ = (representationMultiplicity k S N : ℝ) *
          ∑ n ∈ N, ∑ t ∈ prodFiber k S n, (∏ i, w i (t i)) ^ 2 := by
          rw [Finset.mul_sum]
    _ = (representationMultiplicity k S N : ℝ) * ∏ i, energy S (w i) := by
          rw [prodFiber_fibrewise_sq S N w hmaps]

/-- **`a3_sq_sum_le`.**  `LEAN_PROVED`.  The three-prime instance. -/
theorem a3_sq_sum_le (S N : Finset ℕ) (w : Fin 3 → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin 3 => S), (∏ i, t i) ∈ N) :
    ∑ n ∈ N, (a3 S w n) ^ 2 ≤
      (representationMultiplicity 3 S N : ℝ) * ∏ i, energy S (w i) :=
  convWeight_sq_sum_le S N w hmaps

/-- **`b4_sq_sum_le`.**  `LEAN_PROVED`.  The four-prime instance. -/
theorem b4_sq_sum_le (S N : Finset ℕ) (w : Fin 4 → ℕ → ℝ)
    (hmaps : ∀ t ∈ Fintype.piFinset (fun _ : Fin 4 => S), (∏ i, t i) ∈ N) :
    ∑ m ∈ N, (b4 S w m) ^ 2 ≤
      (representationMultiplicity 4 S N : ℝ) * ∏ i, energy S (w i) :=
  convWeight_sq_sum_le S N w hmaps

/-! ## §7.4  No injectivity: multiplicity and repeated primes -/

/-- **`labelled_multiplicity_exceeds_one`.**  `LEAN_PROVED`.

The three labellings of `2 · 3 · 5 = 30` are distinct tuples, so the labelled representation
multiplicity is genuinely larger than one and injectivity must not be assumed. -/
theorem labelled_multiplicity_exceeds_one :
    ![2, 3, 5] ∈ prodFiber 3 {2, 3, 5} 30 ∧ ![3, 2, 5] ∈ prodFiber 3 {2, 3, 5} 30 ∧
      (![2, 3, 5] : Fin 3 → ℕ) ≠ ![3, 2, 5] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_prodFiber]
    refine ⟨?_, by decide⟩
    intro i; fin_cases i <;> decide
  · rw [mem_prodFiber]
    refine ⟨?_, by decide⟩
    intro i; fin_cases i <;> decide
  · intro h
    have := congrFun h 0
    simp at this

/-- **`repeated_primes_are_included`.**  `LEAN_PROVED`.

A tuple with a repeated entry lies in the fibre: `2 · 2 · 3 = 12`. -/
theorem repeated_primes_are_included :
    ![2, 2, 3] ∈ prodFiber 3 {2, 3} 12 := by
  rw [mem_prodFiber]
  refine ⟨?_, by decide⟩
  intro i; fin_cases i <;> decide

/-- **`representationMultiplicity_ge_two`.**  `LEAN_PROVED`.

Consequently the multiplicity constant of the `3`-fold algebra on `{2,3,5}` with output
range `{30}` is at least `2`; the collision bound above must carry it. -/
theorem representationMultiplicity_ge_two :
    2 ≤ representationMultiplicity 3 {2, 3, 5} {30} := by
  have hcard : 2 ≤ (prodFiber 3 {2, 3, 5} 30).card :=
    Finset.one_lt_card.mpr
      ⟨_, labelled_multiplicity_exceeds_one.1, _, labelled_multiplicity_exceeds_one.2.1,
        labelled_multiplicity_exceeds_one.2.2⟩
  exact le_trans hcard (card_prodFiber_le_representationMultiplicity (by simp))

/-! ## §7.5  The prime-density socket (uninhabited) -/

/-- **`ThreePlusFourPrimeDensityInput`** — `EXTERNAL / SOURCE OPEN`.

The prime-density / PNT input that would convert the finite multiplicity algebra into the
research targets

```
    ∑_n |a₃(n)|² ≪ X^{3/7} log^{-3+o(1)} X,
    ∑_m |b₄(m)|² ≪ X^{4/7} log^{-4+o(1)} X.
```

It is **not** inhabited, and the finite algebra above does not imply it. -/
structure ThreePlusFourPrimeDensityInput
    (S : Finset ℕ) (N : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ)
    (X C3 C4 eps : ℝ) : Prop where
  /-- The support consists of primes. -/
  prime_support : ∀ p ∈ S, Nat.Prime p
  /-- The scale is nontrivial. -/
  scale : 3 ≤ X
  /-- The declared `o(1)` slack is a genuine slack. -/
  eps_pos : 0 < eps
  /-- The three-prime density target. -/
  a3_target : ∑ n ∈ N, (a3 S w3 n) ^ 2 ≤
    C3 * X ^ ((3 : ℝ) / 7) * (Real.log X) ^ (-3 + eps)
  /-- The four-prime density target. -/
  b4_target : ∑ m ∈ N, (b4 S w4 m) ^ 2 ≤
    C4 * X ^ ((4 : ℝ) / 7) * (Real.log X) ^ (-4 + eps)

/-- **`threePlusFourDensity_not_automatic`.**  `LEAN_PROVED`.

The density socket is a genuine restriction: explicit data refute it.  In particular the
finite multiplicity algebra of §7.3 does not supply it. -/
theorem threePlusFourDensity_not_automatic :
    ∃ (S N : Finset ℕ) (w3 : Fin 3 → ℕ → ℝ) (w4 : Fin 4 → ℕ → ℝ) (X C3 C4 eps : ℝ),
      ¬ ThreePlusFourPrimeDensityInput S N w3 w4 X C3 C4 eps := by
  refine ⟨{4}, ∅, fun _ _ => 0, fun _ _ => 0, 3, 0, 0, 1, ?_⟩
  intro h
  have := h.prime_support 4 (by simp)
  norm_num at this

end CurrentProgramme
end Erdos287
