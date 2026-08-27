import Mathlib
import RequestProject.Erdos287.FixedCertificateSingletonParameters

/-!
# The Ford fragmentation interface and the canonical singleton theorem (V13, Parts E–H)

## Part E — status of the fragmentation input

Ford–Maynard Lemma 7.17 is a **published analytic/combinatorial fragmentation input**.  It
is *not* formalised in this repository, and this file does not pretend otherwise: no proof
of it is attempted and no inhabitant of the interface below is ever produced.

What is introduced here is the smallest honest data structure recording the *output* that
the downstream singleton argument consumes: two fragmented sides
`u = u₁ ⋯ u_s`, `v = v₁ ⋯ v_r` with `1 ≤ s, r ≤ 20`, normalised logarithmic sizes summing
to `1`, each side having at most one *terminal* piece (of size in `[0, σ/3]`) and all other
pieces *nonterminal* (of size in `(σ/3, σ]`).

Classification: `CONDITIONAL_INTERFACE / PUBLISHED_SOURCE`.

### Terminal-position convention

Ford's fragmentation peels pieces off greedily and leaves a small remainder, so the
terminal piece, when it exists, is the **last** one.  That convention is recorded
explicitly by the fields `tu_last` / `tv_last`; without it, the canonical selection of the
*first* factor would not be guaranteed nonterminal (hostile check 6).

## Part F — the canonical singleton theorem

The main new kernel theorem.  Two facts are proved:

* `fragment_seven_le_card` — a fragmentation of total normalised size `1` into at most
  `s + r` pieces of size `≤ σ < 1/6` needs `s + r ≥ 7`.  In particular
  `fragment_not_both_singleton`: `s = r = 1` is impossible.  (The request's argument via
  `1 ≤ 2σ/3` is also recorded, as `fragment_singleton_terminal_contradiction`, but it
  needs both singletons to be terminal, which the interface does not force; the size bound
  proved here is unconditional on terminality and strictly stronger.)
* `canonical_singleton_typeII` — the canonically selected piece (the first `u`-factor if
  `s ≥ 2`, otherwise the first `v`-factor, which exists since then `r ≥ 6`) is nonterminal,
  hence `σ/3 < z ≤ σ`, hence by the parameter ledger `ε < z ≤ ε + σ`.  The selected
  Type-II set is therefore a **singleton**.

## Part G — real-power translation

`singleton_real_power_window` transports the normalised-exponent statement to the physical
support statement `X^{σ/3} < m ≤ X^σ`, and `singleton_real_power_window_shifted` to
`(X/2)^ε < m ≤ X^{ε+σ}`.

## Part H — the two singleton grammar types

`SingletonClass` distinguishes the Möbius singleton (selected from the `u` side) from the
model singleton (selected from the `v` side).  **No analytic estimate is formalised for
either class, and no provider dictionary is asserted** (see the firewall note below).
`singleton_complement_depth_le_39` is the finite arithmetic `s + r ≤ 40`, one factor
selected, hence complement depth `≤ 39`.

## Provider firewall

Nothing in this file asserts `MobiusSingleton → Gate1B`, `ModelSingleton → QK56`, or any
map from the singleton Type-II input to `Gate1A`, `H8`/`H9`, Pascadi, or a well-factorable
theorem.  `SingletonClass` is a *tag*, with no inhabited bridge to any historical gate
object.  In particular `depth = 1` is not claimed to imply any such object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace Singleton

/-! ## Part H (data) — the two singleton grammar types -/

/-- The two generated singleton grammars.

* `mobius` — the selected factor comes from the `u` side; its coefficient grammar is
  `ξ(m) = μ(m) × (box factor) × (Mellin/Perron factor) × (prime-order separation factor)`;
* `model` — the selected factor comes from the `v` side; its coefficient grammar is
  `ξ(m) = m^{it} × (box factor) × (Mellin/Perron factor) × (prime-order separation factor)`.

This is a **tag only**.  No analytic estimate is attached to either constructor here, and
no provider dictionary is asserted. -/
inductive SingletonClass
  | mobius
  | model
  deriving DecidableEq, Repr

/-! ## Part E — the fragmentation certificate -/

/-- **`FordSmoothFragmentCertificate`** — `CONDITIONAL_INTERFACE / PUBLISHED_SOURCE`.

The output data of the Ford–Maynard fragmentation on the smooth branch, at smoothness
exponent `sigma`.  Nothing in this project inhabits it; it is never assumed globally. -/
structure FordSmoothFragmentCertificate (sigma : ℝ) where
  /-- Number of pieces on the `u` side. -/
  s : ℕ
  /-- Number of pieces on the `v` side. -/
  r : ℕ
  /-- Normalised logarithmic sizes of the `u` pieces, indexed `0, …, s−1`. -/
  zu : ℕ → ℝ
  /-- Normalised logarithmic sizes of the `v` pieces, indexed `0, …, r−1`. -/
  zv : ℕ → ℝ
  /-- The `u` side is nonempty. -/
  s_pos : 1 ≤ s
  /-- At most twenty pieces on the `u` side. -/
  s_le : s ≤ 20
  /-- The `v` side is nonempty. -/
  r_pos : 1 ≤ r
  /-- At most twenty pieces on the `v` side. -/
  r_le : r ≤ 20
  /-- Index of the terminal `u` piece, if there is one (at most one per side). -/
  tu : Option ℕ
  /-- Index of the terminal `v` piece, if there is one (at most one per side). -/
  tv : Option ℕ
  /-- Terminal-position convention: the terminal `u` piece is the last one. -/
  tu_last : ∀ i ∈ tu, i = s - 1
  /-- Terminal-position convention: the terminal `v` piece is the last one. -/
  tv_last : ∀ i ∈ tv, i = r - 1
  /-- A terminal `u` piece has size in `[0, σ/3]`. -/
  zu_term : ∀ i ∈ tu, 0 ≤ zu i ∧ zu i ≤ sigma / 3
  /-- A terminal `v` piece has size in `[0, σ/3]`. -/
  zv_term : ∀ i ∈ tv, 0 ≤ zv i ∧ zv i ≤ sigma / 3
  /-- Every nonterminal `u` piece has size in `(σ/3, σ]`. -/
  zu_nonterm : ∀ i, i < s → tu ≠ some i → sigma / 3 < zu i ∧ zu i ≤ sigma
  /-- Every nonterminal `v` piece has size in `(σ/3, σ]`. -/
  zv_nonterm : ∀ i, i < r → tv ≠ some i → sigma / 3 < zv i ∧ zv i ≤ sigma
  /-- The total normalised logarithmic size of all pieces is `1`. -/
  total : (∑ i ∈ Finset.range s, zu i) + (∑ i ∈ Finset.range r, zv i) = 1

namespace FordSmoothFragmentCertificate

variable {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma)

/-- Every `u` piece — terminal or not — has size at most `σ`. -/
theorem zu_le_sigma (hs : 0 ≤ sigma) {i : ℕ} (hi : i < c.s) : c.zu i ≤ sigma := by
  by_cases h : c.tu = some i
  · have := (c.zu_term i (by rw [h]; rfl)).2
    linarith
  · exact (c.zu_nonterm i hi h).2

/-- Every `v` piece — terminal or not — has size at most `σ`. -/
theorem zv_le_sigma (hs : 0 ≤ sigma) {i : ℕ} (hi : i < c.r) : c.zv i ≤ sigma := by
  by_cases h : c.tv = some i
  · have := (c.zv_term i (by rw [h]; rfl)).2
    linarith
  · exact (c.zv_nonterm i hi h).2

/-- **Fragmentation size bound.**  `1 ≤ (s + r)·σ`. -/
theorem total_le_card_mul_sigma (hs : 0 ≤ sigma) :
    1 ≤ ((c.s : ℝ) + (c.r : ℝ)) * sigma := by
  have hu : (∑ i ∈ Finset.range c.s, c.zu i) ≤ (c.s : ℝ) * sigma := by
    calc (∑ i ∈ Finset.range c.s, c.zu i)
        ≤ ∑ _i ∈ Finset.range c.s, sigma :=
          Finset.sum_le_sum fun i hi => c.zu_le_sigma hs (Finset.mem_range.1 hi)
      _ = (c.s : ℝ) * sigma := by simp [mul_comm]
  have hv : (∑ i ∈ Finset.range c.r, c.zv i) ≤ (c.r : ℝ) * sigma := by
    calc (∑ i ∈ Finset.range c.r, c.zv i)
        ≤ ∑ _i ∈ Finset.range c.r, sigma :=
          Finset.sum_le_sum fun i hi => c.zv_le_sigma hs (Finset.mem_range.1 hi)
      _ = (c.r : ℝ) * sigma := by simp [mul_comm]
  have := c.total
  nlinarith [hu, hv]

end FordSmoothFragmentCertificate

/-! ## Part F — the canonical singleton theorem -/

variable {eps : ℝ}

/-- **At least seven pieces.**  With `σ < 1/6`, a fragmentation of total normalised size
`1` into pieces of size at most `σ` must have `s + r ≥ 7`. -/
theorem fragment_seven_le_card (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps)) : 7 ≤ c.s + c.r := by
  by_contra hcon
  push_neg at hcon
  have hsr : c.s + c.r ≤ 6 := by omega
  have hcast : ((c.s : ℝ) + (c.r : ℝ)) ≤ 6 := by
    have : ((c.s + c.r : ℕ) : ℝ) ≤ (6 : ℕ) := Nat.cast_le.2 hsr
    push_cast at this
    linarith
  have hb := c.total_le_card_mul_sigma (le_of_lt (sigma_pos h))
  have h6 := six_sigma_lt_one h
  nlinarith [sigma_pos h]

/-- **`s = r = 1` is impossible.**  Immediate from `fragment_seven_le_card`. -/
theorem fragment_not_both_singleton (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps)) : ¬ (c.s = 1 ∧ c.r = 1) := by
  intro hc
  have := fragment_seven_le_card h c
  omega

/-- The request's own version of the previous statement: *if* both sides are single
terminal pieces, the total size would be at most `2σ/3 < 1`.  This needs the terminality
hypothesis, which the interface does not force — which is why
`fragment_not_both_singleton` is proved from the unconditional size bound instead. -/
theorem fragment_singleton_terminal_contradiction (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps))
    (hs : c.s = 1) (hr : c.r = 1) (htu : c.tu = some 0) (htv : c.tv = some 0) : False := by
  have hu : c.zu 0 ≤ sigmaOf eps / 3 := (c.zu_term 0 (by rw [htu]; rfl)).2
  have hv : c.zv 0 ≤ sigmaOf eps / 3 := (c.zv_term 0 (by rw [htv]; rfl)).2
  have htot := c.total
  rw [hs, hr] at htot
  simp only [Finset.sum_range_one] at htot
  have := two_sigma_div_three_lt_one h
  linarith

/-- If the `u` side is a single piece then the `v` side has at least six. -/
theorem fragment_r_ge_of_s_eq_one (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps)) (hs : c.s = 1) : 6 ≤ c.r := by
  have := fragment_seven_le_card h c
  omega

/-- The canonically selected piece: the first `u`-factor if `s ≥ 2`, otherwise the first
`v`-factor. -/
noncomputable def chosenSize {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) : ℝ :=
  if 2 ≤ c.s then c.zu 0 else c.zv 0

/-- The grammar class of the canonically selected piece. -/
def chosenClass {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) : SingletonClass :=
  if 2 ≤ c.s then SingletonClass.mobius else SingletonClass.model

/-- The label of the canonically selected piece: its side tag and its index. -/
def chosenLabel {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) :
    SingletonClass × ℕ := (chosenClass c, 0)

/-- The selected Type-II set `E`. -/
def chosenTypeIISet {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) :
    Finset (SingletonClass × ℕ) := {chosenLabel c}

/-- **The selected piece is nonterminal.**  This is where the terminal-position convention
`tu_last` / `tv_last` is used: index `0` can only be terminal on a side of length `1`, and
the selected side always has length `≥ 2`. -/
theorem chosen_nonterminal (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps)) :
    sigmaOf eps / 3 < chosenSize c ∧ chosenSize c ≤ sigmaOf eps := by
  unfold chosenSize
  by_cases hs : 2 ≤ c.s
  · rw [if_pos hs]
    refine c.zu_nonterm 0 (by omega) ?_
    intro hcon
    have := c.tu_last 0 (by rw [hcon]; rfl)
    omega
  · rw [if_neg hs]
    have hs1 : c.s = 1 := by have := c.s_pos; omega
    have hr : 6 ≤ c.r := fragment_r_ge_of_s_eq_one h c hs1
    refine c.zv_nonterm 0 (by omega) ?_
    intro hcon
    have := c.tv_last 0 (by rw [hcon]; rfl)
    omega

/-- **`canonical_singleton_typeII`** — the main new kernel theorem.

Given a valid Ford fragmentation certificate at the ledger exponent `σ = ν₀ − 2ε`:

* the canonical branch is well defined (`s ≥ 2`, or else `s = 1` and `r ≥ 6 ≥ 2`);
* the chosen piece is nonterminal, so `σ/3 < z ≤ σ`;
* hence, by the parameter ledger, `ε < z ≤ ε + σ`.

The selected Type-II subset can therefore be taken to be a singleton. -/
theorem canonical_singleton_typeII (h : AdmissibleEps eps)
    (c : FordSmoothFragmentCertificate (sigmaOf eps)) :
    (2 ≤ c.s ∨ (c.s = 1 ∧ 2 ≤ c.r)) ∧
      sigmaOf eps / 3 < chosenSize c ∧ chosenSize c ≤ sigmaOf eps ∧
      eps < chosenSize c ∧ chosenSize c ≤ eps + sigmaOf eps := by
  obtain ⟨hnt1, hnt2⟩ := chosen_nonterminal h c
  refine ⟨?_, hnt1, hnt2, ?_, ?_⟩
  · by_cases hs : 2 ≤ c.s
    · exact Or.inl hs
    · have hs1 : c.s = 1 := by have := c.s_pos; omega
      exact Or.inr ⟨hs1, by have := fragment_r_ge_of_s_eq_one h c hs1; omega⟩
  · have := epsilon_lt_sigma_div_three h
    linarith
  · have := h.1
    linarith

/-- **`canonical_singleton_card_eq_one`** — the selected Type-II set has exactly one
element. -/
theorem canonical_singleton_card_eq_one {sigma : ℝ}
    (c : FordSmoothFragmentCertificate sigma) : (chosenTypeIISet c).card = 1 :=
  Finset.card_singleton _

/-- **`singleton_supersedes_depth_five`** — the old `|E| ≤ 5` target is no longer
controlling: the canonical selection gives `|E| = 1 < 5`. -/
theorem singleton_supersedes_depth_five {sigma : ℝ}
    (c : FordSmoothFragmentCertificate sigma) :
    (chosenTypeIISet c).card < 5 ∧ (chosenTypeIISet c).card ≤ 5 := by
  rw [canonical_singleton_card_eq_one]
  exact ⟨by norm_num, by norm_num⟩

/-- The chosen class really is `mobius` exactly when the `u` side was selected. -/
theorem chosenClass_mobius_iff {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) :
    chosenClass c = SingletonClass.mobius ↔ 2 ≤ c.s := by
  unfold chosenClass
  by_cases hs : 2 ≤ c.s <;> simp [hs]

/-! ## Part H — complement depth -/

/-- The total fragmentation depth `s + r`. -/
def fragmentDepth {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) : ℕ := c.s + c.r

/-- `s + r ≤ 40`. -/
theorem fragment_depth_le_40 {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) :
    fragmentDepth c ≤ 40 := by
  have := c.s_le; have := c.r_le
  unfold fragmentDepth; omega

/-- `2 ≤ s + r`, so the complement is a genuine subtraction. -/
theorem two_le_fragment_depth {sigma : ℝ} (c : FordSmoothFragmentCertificate sigma) :
    2 ≤ fragmentDepth c := by
  have := c.s_pos; have := c.r_pos
  unfold fragmentDepth; omega

/-- **`singleton_complement_depth_le_39`.**  At most `40` fragmentation factors, exactly
one of which is selected as the Type-II singleton, leaves a complement of depth at most
`39` — not `40` (hostile check 7). -/
theorem singleton_complement_depth_le_39 {sigma : ℝ}
    (c : FordSmoothFragmentCertificate sigma) :
    fragmentDepth c - (chosenTypeIISet c).card ≤ 39 ∧
      fragmentDepth c - (chosenTypeIISet c).card = fragmentDepth c - 1 ∧
      1 ≤ fragmentDepth c - (chosenTypeIISet c).card := by
  have h40 := fragment_depth_le_40 c
  have h2 := two_le_fragment_depth c
  rw [canonical_singleton_card_eq_one]
  refine ⟨by omega, rfl, by omega⟩

/-! ## Part G — real-power translation -/

/-- **Physical support statement.**  If `X > 1`, `m > 0` and the normalised logarithmic
size of `m` in base `X` is `z` with `σ/3 < z ≤ σ`, then `X^{σ/3} < m ≤ X^σ`. -/
theorem singleton_real_power_window {X m z sigma : ℝ}
    (hX : 1 < X) (hm : 0 < m) (hz : Real.log m / Real.log X = z)
    (h1 : sigma / 3 < z) (h2 : z ≤ sigma) :
    X ^ (sigma / 3) < m ∧ m ≤ X ^ sigma := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogm : Real.log m = z * Real.log X := by
    field_simp at hz
    linarith [hz]
  have hmeq : m = X ^ z := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < X), mul_comm, ← hlogm, Real.exp_log hm]
  constructor
  · rw [hmeq]
    exact Real.rpow_lt_rpow_left_iff hX |>.2 h1
  · rw [hmeq]
    exact Real.rpow_le_rpow_left_iff hX |>.2 h2

/-- The shifted (convention-correct) form: `(X/2)^ε < m ≤ X^{ε+σ}`. -/
theorem singleton_real_power_window_shifted (h : AdmissibleEps eps) {X m z : ℝ}
    (hX : 1 < X) (hm : 0 < m) (hz : Real.log m / Real.log X = z)
    (h1 : sigmaOf eps / 3 < z) (h2 : z ≤ sigmaOf eps) :
    (X / 2) ^ eps < m ∧ m ≤ X ^ (eps + sigmaOf eps) := by
  obtain ⟨hlow, hhigh⟩ := singleton_real_power_window hX hm hz h1 h2
  have heps := h.1
  constructor
  · have hle : (X / 2) ^ eps ≤ X ^ eps :=
      Real.rpow_le_rpow (by linarith) (by linarith) (le_of_lt heps)
    have hmono : X ^ eps < X ^ (sigmaOf eps / 3) :=
      Real.rpow_lt_rpow_left_iff hX |>.2 (epsilon_lt_sigma_div_three h)
    linarith
  · have : X ^ sigmaOf eps ≤ X ^ (eps + sigmaOf eps) :=
      Real.rpow_le_rpow_left_iff hX |>.2 (by linarith)
    linarith

end Singleton
end Erdos287
