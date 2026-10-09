import RequestProject.Erdos287.PostV71V87.Physical

/-!
# Erdős #287 — high-shell scope firewall, terminal-window firewall, open frontier

## Three-zone picture (V87 high-shell result, repaired domain)

1. **Below `q_*` (PROVED):** every prime row is active and carries the fingerprint
   (`zone_one_below_qstar`).
2. **Sufficiently high shells:**
   * shells `(X, 2X]` with `X ≥ ⌊M/2⌋` are *totally* empty — **PROVED** unconditionally
     (`highShell_trivial`);
   * "almost all rows empty" at lower admissible thresholds `X ≥ X0(M)` is the explicit
     provider `HighShellExtinction X0 ε` — **CONDITIONAL** (the analytic estimate is not
     formalised; we only derive `highShell_some_empty_row` from it).
3. **Intermediate scales `q_* < X < X0(M)`: OPEN** (`IntermediateScaleControl287`).

**Not claimed:** almost-empty shells immediately above `q_*`; `q_*` being a sharp
active/empty transition (`NearbyTransition287`, a fictitious provider recorded only to be
fenced off); control of every intermediate scale.

## Terminal-window firewall

`polylog_window_not_excluded`: for every `c` and every `B ≥ 2`, the repaired recurrence
conclusion `c · g(log D) ≤ D/q` holds **automatically** whenever `q ≤ D/(log D)^B` and `D` is
large.  Hence the recurrence theorem alone does **not** exclude a terminal window
`M/(log M)^B < q_* ≪ M/T(M)`.

## Open frontier

* `Proximity287` — substantial empty-row information at scales `(q_*, K q_*]` (OPEN).
* `CrossScaleSynchronization287 M0` — no exact word with `M ≥ M0` realises the full
  cross-scale package `CrossScaleRealisation` (OPEN).  We prove that *every* exact word
  realises the package (`realisation_of_exact`), so this interface is **equivalent** to the
  nonexistence of counterexamples with `M ≥ M0` (`crossScale_iff_tail`): it is not weaker than
  the tail of #287, and it is the actual dependency of the hypothetical tail closure
  `tail_closure_of_crossScale`.

Neither provider is constructed anywhere in this subtree.
-/

open Real
open scoped BigOperators

namespace Erdos287.PostV71V87

/-! ## Shells -/

/-- Active primes in the shell `(X, 2X]`. -/
noncomputable def Word.activeShell (W : Word) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter (fun p => p.Prime ∧ W.Active p)

/-- Number of primes in the shell `(X, 2X]`. -/
def shellPrimeCount (X : ℕ) : ℕ := ((Finset.Ioc X (2 * X)).filter Nat.Prime).card

/-- **Zone 1 (PROVED).**  Below `q_*` every prime row is active and fingerprinted. -/
theorem zone_one_below_qstar (W : ExactWord) {p : ℕ} (hp : p.Prime) (hlt : p < W.qstar) :
    W.Active p ∧ 2 ≤ (W.layer p).card ∧ (p : ℤ) ∣ (W.sigma p).num :=
  W.shell_fingerprint hp hlt

/-- **(Provider, CONDITIONAL.)**  High-shell extinction above the threshold `X0(M)`: the
active primes of every shell `(X, 2X]` with `X ≥ X0(M)` form at most an `ε`-fraction of the
shell's primes. -/
def HighShellExtinction (X0 : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ W : ExactWord, 1 < W.a → ∀ X : ℕ, X0 W.M ≤ X →
    ((W.activeShell X).card : ℝ) ≤ ε * shellPrimeCount X

/-- **Zone 2, trivial range (PROVED).**  Shells above `⌊M/2⌋` are completely empty. -/
theorem highShell_trivial : HighShellExtinction (fun M => M / 2) 0 := by
  intro W ha X hX
  simp only at hX
  have : W.activeShell X = ∅ := by
    classical
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Word.activeShell, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, _⟩, hpp, hact⟩ := hp
    exact W.not_active_of_lt_two_mul hpp (by omega) hact
  rw [this]; simp

/-- Bertrand: every shell `(X, 2X]` with `X ≥ 1` contains a prime. -/
theorem shellPrimeCount_pos {X : ℕ} (hX : 1 ≤ X) : 0 < shellPrimeCount X := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul X (by omega)
  exact Finset.card_pos.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1, h2⟩, hp⟩⟩

/-- **Zone 2 (CONDITIONAL consequence).**  Under `HighShellExtinction X0 ε` with `ε < 1`, every
shell above the threshold contains an empty prime row. -/
theorem highShell_some_empty_row {X0 : ℕ → ℕ} {ε : ℝ} (h : HighShellExtinction X0 ε)
    (hε : ε < 1) (W : ExactWord) (ha : 1 < W.a) {X : ℕ} (hX : X0 W.M ≤ X) (hX1 : 1 ≤ X) :
    ∃ p, p.Prime ∧ X < p ∧ p ≤ 2 * X ∧ ¬ W.Active p := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.Ioc X (2 * X)).filter Nat.Prime ⊆ W.activeShell X := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    simp only [Word.activeShell, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨hp.1, hp.2, hc p hp.2 hp.1.1 hp.1.2⟩
  have h1 : (shellPrimeCount X : ℝ) ≤ (W.activeShell X).card := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 := h W ha X hX
  have h3 : (0 : ℝ) < shellPrimeCount X := by exact_mod_cast shellPrimeCount_pos hX1
  nlinarith

/-- **Zone 3 (OPEN).**  Control of every intermediate scale between `q_*` and `X0(M)`. -/
def IntermediateScaleControl287 (X0 : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ W : ExactWord, 1 < W.a → ∀ X : ℕ, W.qstar ≤ X → X < X0 W.M →
    ((W.activeShell X).card : ℝ) ≤ ε * shellPrimeCount X

/-- **Fictitious provider (never assumed).**  "`q_*` is a sharp active/empty transition":
every prime row in `(q_*, 2 q_*]` is empty for large words.  Recorded only so that closure
statements can be shown not to depend on it. -/
def NearbyTransition287 : Prop :=
  ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
    ∀ p, p.Prime → W.qstar < p → p ≤ 2 * W.qstar → ¬ W.Active p

/-! ## Open frontier interfaces -/

open Classical in
/-- **OPEN — `Proximity287`.**  Substantial empty-row information at scales quantitatively
close to `q_*`: for some fixed `K ≥ 2`, in all large exact words at most half of the primes in
`(q_*, K q_*]` have active rows. -/
def Proximity287 : Prop :=
  ∃ K : ℕ, 2 ≤ K ∧ ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
    2 * ((Finset.Ioc W.qstar (K * W.qstar)).filter (fun p => p.Prime ∧ W.Active p)).card ≤
      ((Finset.Ioc W.qstar (K * W.qstar)).filter Nat.Prime).card

/-- The fictitious sharp transition would already give `Proximity287` (with `K = 2`); it is
therefore at least as strong as an OPEN statement and is not available. -/
theorem nearbyTransition_implies_proximity (h : NearbyTransition287) : Proximity287 := by
  classical
  obtain ⟨M0, hM0⟩ := h
  refine ⟨2, le_refl 2, M0, fun W ha hM => ?_⟩
  rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)]
  · simp
  · intro p hp hpa
    rw [Finset.mem_Ioc] at hp
    exact hM0 W ha hM p hpa.1 hp.1 hp.2 hpa.2

/-- **Scope firewall.**  Any derivation of `Proximity287` from high-shell extinction at the
trivially available threshold `⌊M/2⌋` would prove `Proximity287` outright. -/
theorem proximity_not_from_trivial_highShell
    (h : HighShellExtinction (fun M => M / 2) 0 → Proximity287) : Proximity287 :=
  h highShell_trivial

/-- The full cross-scale package realised by an exact word. -/
structure CrossScaleRealisation (W : ExactWord) : Prop where
  /-- Repeated minimal-ceiling guard triples. -/
  guards : ∀ y ∈ W.internalMultiples W.qstar,
    W.x (y - 1) = true ∧ W.x y = false ∧ W.x (y + 1) = true
  /-- All complete rows below `q_*` active, with fingerprint. -/
  rows_below : ∀ p, p.Prime → p < W.qstar → W.Active p ∧ (p : ℤ) ∣ (W.sigma p).num
  /-- Polynomial maximal-carrier reserve. -/
  carrier_reserve : ∀ p ∈ W.reservePrimes, p ≤ W.P p ∧ W.D < W.P p ^ 4
  /-- High shells (above `⌊M/2⌋`) empty. -/
  high_shells : ∀ X, W.M / 2 ≤ X → W.activeShell X = ∅
  /-- All lower carry digits: no prime divides the reduced denominator of the mass. -/
  carry_digits : ∀ p, p.Prime → ¬ p ∣ (∑ n ∈ W.A, (1 : ℚ) / n).den
  /-- Exact mass one. -/
  exact_mass : ∑ n ∈ W.A, (1 : ℚ) / n = 1

/-- **Every exact word realises the full cross-scale package** (all components
are proved in this subtree). -/
theorem realisation_of_exact (W : ExactWord) : CrossScaleRealisation W where
  guards := fun y hy => W.guard_at_internal_qstar hy
  rows_below := fun p hp hlt =>
    ⟨(W.shell_fingerprint hp hlt).1, (W.shell_fingerprint hp hlt).2.2⟩
  carrier_reserve := fun p hp => by
    have h := W.mem_reservePrimes.1 hp
    exact W.toWord.carrier_reserve h.1 h.2.1 h.2.2
  high_shells := fun X hX => by
    classical
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Word.activeShell, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact W.not_active_of_lt_two_mul hp.2.1 (by omega) hp.2.2
  carry_digits := fun p hp => by rw [W.mass]; simpa using hp.one_lt.ne'
  exact_mass := W.mass

/-- **OPEN — `CrossScaleSynchronization287`.**  No exact word with `M ≥ M0` realises the full
cross-scale package. -/
def CrossScaleSynchronization287 (M0 : ℕ) : Prop :=
  ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → ¬ CrossScaleRealisation W

/-- **Exposure theorem.**  `CrossScaleSynchronization287 M0` is equivalent to the
nonexistence of exact words with `a > 1`, `M ≥ M0`. -/
theorem crossScale_iff_tail (M0 : ℕ) :
    CrossScaleSynchronization287 M0 ↔ ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M → False := by
  constructor
  · intro h W ha hM; exact h W ha hM (realisation_of_exact W)
  · intro h W ha hM _; exact h W ha hM

/-- Finite exclusion below `M0` (an explicit, unproved input). -/
def FiniteExclusionBelow (M0 : ℕ) : Prop :=
  ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, A.max' h.nonempty < M0 → False

/-- **Hypothetical tail closure (CONDITIONAL on `CrossScaleSynchronization287`).** -/
theorem tail_closure_of_crossScale {M0 : ℕ} (h : CrossScaleSynchronization287 M0)
    (A : Finset ℕ) (hA : Erdos287Counterexample A) : A.max' hA.nonempty < M0 := by
  by_contra hc
  push_neg at hc
  have hW := ofCounterexample_one_lt_a hA
  exact h (ofCounterexample hA) hW hc (realisation_of_exact _)

/-- **Conditional global statement.**  `CrossScaleSynchronization287 M0` together with the
finite exclusion below `M0` would give Erdős #287.  Both inputs are OPEN / unproved. -/
theorem erdos287_of_crossScale_and_finite {M0 : ℕ} (h : CrossScaleSynchronization287 M0)
    (hfin : FiniteExclusionBelow M0) (A : Finset ℕ) : ¬ Erdos287Counterexample A :=
  fun hA => hfin A hA (tail_closure_of_crossScale h A hA)

/-! ## Terminal-window firewall -/

/-- `k · log x ≤ x` for `x ≥ 4k²`, `k > 0`. -/
theorem mul_log_le_self {k x : ℝ} (hk : 0 < k) (hx : 4 * k ^ 2 ≤ x) (hx1 : 1 ≤ x) :
    k * Real.log x ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have h1 := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : 2 * k ≤ Real.sqrt x := by
    rw [show 2 * k = Real.sqrt ((2 * k) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsx := Real.mul_self_sqrt hx0
  have : Real.log x ≤ 2 * Real.sqrt x := by linarith [show Real.sqrt x / (1 / 2) = 2 * Real.sqrt x by ring]
  nlinarith [Real.sqrt_nonneg x]

/-- **Terminal-window firewall.**  For every constant `c > 0` and every `B ≥ 2`, the repaired
recurrence conclusion `c · g(log D) ≤ D/q` holds automatically for every `q ≤ D/(log D)^B`
once `D` is large.  Hence superlogarithmic recurrence alone cannot exclude a polylogarithmic
terminal window `M/(log M)^B < q_* ≪ M/T(M)`. -/
theorem polylog_window_not_excluded (c : ℝ) (hc : 0 < c) (B : ℕ) (hB : 2 ≤ B) :
    ∃ D0 : ℝ, ∀ D : ℝ, D0 ≤ D → ∀ q : ℝ, 0 < q → q ≤ D / Real.log D ^ B →
      c * gRec (Real.log D) ≤ D / q := by
  refine ⟨Real.exp (max 256 (4 * c ^ 2)), fun D hD q hq hqD => ?_⟩
  have hDpos : 0 < D := lt_of_lt_of_le (Real.exp_pos _) hD
  set x := Real.log D with hxdef
  have hx : max 256 (4 * c ^ 2) ≤ x := by rw [hxdef, Real.le_log_iff_exp_le hDpos]; exact hD
  have hx256 : 256 ≤ x := le_trans (le_max_left _ _) hx
  have hxc : 4 * c ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  -- `c · g(x) ≤ x²`
  have hee : Real.exp (Real.exp 1) ≤ x := le_trans exp_exp_one_le_256 hx256
  have hll : 1 ≤ Real.log (Real.log x) := one_le_loglog hx256
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hg : gRec x ≤ x * Real.log x := by
    unfold gRec
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hxpos hlx]
  have hcl : c * Real.log x ≤ x := mul_log_le_self hc hxc (by linarith)
  have h1 : c * gRec x ≤ x ^ 2 := by
    calc c * gRec x ≤ c * (x * Real.log x) := mul_le_mul_of_nonneg_left hg hc.le
      _ = x * (c * Real.log x) := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_left hcl hxpos.le
      _ = x ^ 2 := by ring
  have h2 : x ^ 2 ≤ x ^ B := pow_le_pow_right₀ (by linarith) hB
  have hxB : 0 < x ^ B := pow_pos hxpos B
  have h3 : x ^ B ≤ D / q := by
    rw [le_div_iff₀ hq]
    rw [le_div_iff₀ hxB] at hqD
    linarith
  linarith

end Erdos287.PostV71V87
