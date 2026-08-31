import Mathlib
import RequestProject.Erdos287.EulerUniformityLayer3221
import RequestProject.CurrentProgramme.LogRRepairBank

/-!
# CurrentProgramme §3 — the Euler-uniformity firewall

`BALANCED7-EULER-UNIFORMITY45` — research-audited, **externally audited** formally.

The research-audited principal identity is

```
    J_P(z) = ∑_{q ≤ z, (q, 2P) = 1} μ(q)/φ(q) · log(z/q) = 2B(P) + O_A(log^{-A} z),
```

with the metadata `F_P(w) = H_P(w)/ζ(1+w)`, `H_P(0) = 2B(P)`, `H_P(w) = O(1)` on the audited
contour.

What is banked here is **only**:

* the literal full-`q` sum `jFullQ`, defined over *all* `q ≤ z` coprime to `2P`;
* the exact split of that sum at an arbitrary cutoff `u` (`jFullQ_split`), so that the
  arithmetic content of "full `q`" is visible;
* the firewall `fullQ_identity_not_single_cell`: a full-`q` identity may **not** be handed to
  one SmallQ / SmallR / hard cell whenever the complementary cells contribute;
* an **uninhabited** socket `BalancedSevenFullQEulerIdentityInput` which pins the analytic
  statement to the literal full-`q` sum, together with a conditional consumer.

The analytic theorem itself is *not* proved and *not* inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §3.1  The literal full-`q` sum -/

/-- The full-`q` summation range: every `1 ≤ q ≤ z` coprime to `2P`. -/
noncomputable def eulerQRange (P : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Nat.Coprime q (2 * P))

/-- The literal principal sum `J_P(z) = ∑_{q ≤ z, (q,2P)=1} μ(q)/φ(q) · log(z/q)`. -/
noncomputable def jFullQ (P : ℕ) (z : ℝ) : ℝ :=
  ∑ q ∈ eulerQRange P z, (moebius q : ℝ) / (Nat.totient q : ℝ) * Real.log (z / q)

/-- The part of `J_P(z)` carried by the small variables `q ≤ u`. -/
noncomputable def jFullQSmall (P : ℕ) (z : ℝ) (u : ℕ) : ℝ :=
  ∑ q ∈ (eulerQRange P z).filter (fun q => q ≤ u),
    (moebius q : ℝ) / (Nat.totient q : ℝ) * Real.log (z / q)

/-- The part of `J_P(z)` carried by the large variables `q > u`. -/
noncomputable def jFullQLarge (P : ℕ) (z : ℝ) (u : ℕ) : ℝ :=
  ∑ q ∈ (eulerQRange P z).filter (fun q => ¬ q ≤ u),
    (moebius q : ℝ) / (Nat.totient q : ℝ) * Real.log (z / q)

/-- **`jFullQ_split`.**  `LEAN_PROVED`.

The full-`q` principal sum splits exactly at any cutoff `u`. -/
theorem jFullQ_split (P : ℕ) (z : ℝ) (u : ℕ) :
    jFullQ P z = jFullQSmall P z u + jFullQLarge P z u :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **`eulerQRange_is_unrestricted`.**  `LEAN_PROVED`.

Membership in the full-`q` range is exactly "`1 ≤ q ≤ ⌊z⌋` and `(q, 2P) = 1`": no sector
condition is present. -/
theorem eulerQRange_is_unrestricted {P q : ℕ} {z : ℝ} :
    q ∈ eulerQRange P z ↔ (1 ≤ q ∧ q ≤ ⌊z⌋₊) ∧ Nat.Coprime q (2 * P) := by
  simp [eulerQRange, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-! ## §3.2  The firewall -/

/-- **`fullQ_identity_not_single_cell`.**  `LEAN_PROVED`.

If the full-`q` quantity decomposes as `total = smallQ + smallR + hard` and the two
complementary cells do not cancel, then the full-`q` identity is *not* an identity for the
`smallQ` cell.  The same statement holds with the roles permuted, so a full-`q` analytic
input may not be assigned to any single cell. -/
theorem fullQ_identity_not_single_cell {total sq sr hard : ℝ}
    (hsplit : total = sq + sr + hard) (hne : sr + hard ≠ 0) :
    total ≠ sq ∧ total ≠ sr ∧ total ≠ hard ∨ (sq + hard = 0 ∨ sq + sr = 0) := by
  by_cases h1 : sq + hard = 0
  · exact Or.inr (Or.inl h1)
  by_cases h2 : sq + sr = 0
  · exact Or.inr (Or.inr h2)
  refine Or.inl ⟨?_, ?_, ?_⟩
  · intro h; apply hne; rw [h] at hsplit; linarith
  · intro h; apply h1; rw [h] at hsplit; linarith
  · intro h; apply h2; rw [h] at hsplit; linarith

/-- **`jFullQ_not_smallQ_cell`.**  `LEAN_PROVED`.

Concretely for the principal sum: if the large-`q` part is nonzero then the full-`q` sum is
not the small-`q` sum, so an estimate for `J_P(z)` is not an estimate for the SmallQ cell. -/
theorem jFullQ_not_smallQ_cell {P : ℕ} {z : ℝ} {u : ℕ} (h : jFullQLarge P z u ≠ 0) :
    jFullQ P z ≠ jFullQSmall P z u := by
  intro hEq
  exact h (by have := jFullQ_split P z u; linarith [hEq ▸ this])

/-! ## §3.3  The uninhabited full-`q` socket -/

/-- **`BalancedSevenFullQEulerIdentityInput`** — `EXTERNAL / ANALYTIC / UNINHABITED`.

The analytic input pinned to the *literal* full-`q` sum: the supplied `J` must be `jFullQ`
itself, the Mellin data must satisfy `H_P(0) = 2B(P)` with an `O(1)` contour bound, and the
uniform saving must be a genuine one (`0 < A`). -/
structure BalancedSevenFullQEulerIdentityInput
    (family : Finset ℕ) (J : ℕ → ℝ → ℝ) (HP : ℕ → ℝ → ℝ) (S2 Hbound A : ℝ) : Prop where
  /-- The physical family is nonempty. -/
  family_nonempty : family.Nonempty
  /-- The supplied `J` is the literal full-`q` sum — no sector restriction. -/
  literal_fullQ : ∀ P ∈ family, ∀ z : ℝ, J P z = jFullQ P z
  /-- `H_P(0) = 2B(P)`. -/
  mellin_at_zero : ∀ P ∈ family, HP P 0 = 2 * V23Euler.BofP S2 P
  /-- `H_P(w) = O(1)` on the audited contour (here the real segment `[-1/4, 1/4]`). -/
  contour_bound : ∀ P ∈ family, ∀ w : ℝ, |w| ≤ 1 / 4 → |HP P w| ≤ Hbound
  /-- The uniform principal-term identity with a `log^{-A}` error. -/
  uniform_identity : ∀ P ∈ family, ∀ z : ℝ, 3 ≤ z →
    |J P z - 2 * V23Euler.BofP S2 P| ≤ Hbound * (Real.log z) ^ (-A)
  /-- The saving is genuine. -/
  A_pos : 0 < A

/-- **`fullQEulerIdentity_consumer`** — `CONDITIONAL`.

A consumer of the socket: the literal full-`q` sum then obeys the principal-term identity. -/
theorem fullQEulerIdentity_consumer
    {family : Finset ℕ} {J HP : ℕ → ℝ → ℝ} {S2 Hbound A : ℝ}
    (h : BalancedSevenFullQEulerIdentityInput family J HP S2 Hbound A)
    {P : ℕ} (hP : P ∈ family) {z : ℝ} (hz : 3 ≤ z) :
    |jFullQ P z - 2 * V23Euler.BofP S2 P| ≤ Hbound * (Real.log z) ^ (-A) := by
  have := h.uniform_identity P hP z hz
  rwa [h.literal_fullQ P hP z] at this

/-- **`fullQEulerIdentity_not_automatic`.**  `LEAN_PROVED`.

The socket is a genuine restriction: explicit data refute it.  It is not inhabited here. -/
theorem fullQEulerIdentity_not_automatic :
    ∃ (family : Finset ℕ) (J HP : ℕ → ℝ → ℝ) (S2 Hbound A : ℝ),
      ¬ BalancedSevenFullQEulerIdentityInput family J HP S2 Hbound A := by
  refine ⟨∅, fun _ _ => 0, fun _ _ => 0, 0, 0, 1, ?_⟩
  intro h
  simpa using h.family_nonempty

/-- **`fullQEuler_status_is_external`.**  `LEAN_PROVED`.

Bookkeeping: the Euler-uniformity node is carried by an external interface, while the
`H_P(0) = 2B(P)` normalisation is an internal algebraic theorem of the V24 layer. -/
theorem fullQEuler_status_is_external (S2 : ℝ) (P : ℕ) :
    V23Euler.H0 S2 P = 2 * V23Euler.BofP S2 P ∧
      (∃ (family : Finset ℕ) (J HP : ℕ → ℝ → ℝ) (S2' Hbound A : ℝ),
        ¬ BalancedSevenFullQEulerIdentityInput family J HP S2' Hbound A) :=
  ⟨V24Euler.euler_H0_eq_twoB S2 P, fullQEulerIdentity_not_automatic⟩

end CurrentProgramme
end Erdos287
