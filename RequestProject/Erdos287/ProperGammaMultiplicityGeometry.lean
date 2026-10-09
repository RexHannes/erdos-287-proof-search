import Mathlib

/-!
# Erdős #287 effectivity — physical multiplicity count and shell geometry (§33)

```
MULTIPLICITY COUNT DEFINITION : KERNEL-PROVED
COUNTING INTERPRETATION       : KERNEL-PROVED
NORMALIZED BAND FORM          : KERNEL-PROVED
EXACT SHELL GEOMETRY (all k)  : KERNEL-PROVED
SHELL DISJOINTNESS            : KERNEL-PROVED
NUMERICAL SHELL CLOSURES      : CERTIFICATE-BACKED (never proved here)
ERDŐS #287                    : OPEN
```

With the physical band
```
    A = 7X/10,      Z = 9X/10,
```
the multiplicity count is
```
    N_X(m) = ⌊Z/m⌋ − ⌊A/m⌋,
```
which counts exactly the multiples of `m` lying in `(A, Z]` (`mem_multiplesIn`,
`multiplesIn_card`).

Normalised by `t = m/X`, the count is governed by the *band predicate*
```
    MultAtLeast k t  ↔  ∃ n : ℤ,  7 < 10 n t  and  10 (n + k − 1) t ≤ 9,
```
i.e. by the existence of `k` consecutive integers `n, …, n+k−1` whose `m`-multiples all lie
in `(A, Z]` (`NX_ge_iff`).  The main geometric theorem `multAtLeast_iff` gives, for **every**
`k ≥ 1`, the exact finite union of rational bands describing `{t > 0 : N ≥ k}`:
```
    (0, 9/(10(c_k+k−1))]  ∪  ⋃_{n = a_k}^{c_k − 1} ( 7/(10n), 9/(10(n+k−1)) ],
    a_k = ⌊7(k−1)/2⌋ + 1,   c_k = ⌊7k/2⌋ + 1 .
```
Specialisations `bandsOf_one … bandsOf_seven` print the exact bands for `k = 1, …, 7`.

The shells `Ω_{=k}` are `MultAtLeast k ∧ ¬ MultAtLeast (k+1)`; they are pairwise disjoint
(`shellEq_disjoint`) and `Ω_{=1}` is the exact union of **seven** disjoint normalised
intervals (`shellOne_bands`).

**No analytic numerical bound is proved anywhere in this file.**  The numerical shell
closures (`2.4e-8`, `2.16e-8`, …) enter only as explicit `ShellNumericalCertificate`
objects, whose inhabitation proves nothing about the physical source
(`shellCertificate_not_proved`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Erdos287
namespace Effectivity

/-! ## §33.1  The physical band and the multiplicity count -/

/-- The lower physical band endpoint `A = 7X/10`. -/
def bandLow (X : ℚ) : ℚ := 7 * X / 10

/-- The upper physical band endpoint `Z = 9X/10`. -/
def bandHigh (X : ℚ) : ℚ := 9 * X / 10

/-- `N_X(m) = ⌊Z/m⌋ − ⌊A/m⌋`, the physical multiplicity count. -/
def NX (X : ℚ) (m : ℕ) : ℤ := ⌊bandHigh X / m⌋ - ⌊bandLow X / m⌋

/-- The integers `n` whose `m`-multiple lies in the physical band `(A, Z]`. -/
def multiplesIn (X : ℚ) (m : ℕ) : Finset ℤ :=
  Finset.Ioc ⌊bandLow X / m⌋ ⌊bandHigh X / m⌋

/-- **`mem_multiplesIn`.**  `KERNEL-PROVED`.  Exact interpretation: `n ∈ multiplesIn X m`
iff the multiple `n·m` lies in the band `(A, Z]`. -/
theorem mem_multiplesIn (X : ℚ) {m : ℕ} (hm : 0 < m) (n : ℤ) :
    n ∈ multiplesIn X m ↔ (bandLow X < (n : ℚ) * m ∧ (n : ℚ) * m ≤ bandHigh X) := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  rw [multiplesIn, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]
  rw [div_lt_iff₀ hmQ, le_div_iff₀ hmQ]

/-- **`multiplesIn_card`.**  `KERNEL-PROVED`.  `N_X(m)` is the cardinality of that set. -/
theorem multiplesIn_card (X : ℚ) (m : ℕ) :
    (multiplesIn X m).card = (NX X m).toNat := by
  rw [multiplesIn, Int.card_Ioc, NX]

/-- **`NX_nonneg`.**  `KERNEL-PROVED`. -/
theorem NX_nonneg (X : ℚ) (hX : 0 ≤ X) (m : ℕ) : 0 ≤ NX X m := by
  have hab : bandLow X ≤ bandHigh X := by unfold bandLow bandHigh; linarith
  have h : bandLow X / m ≤ bandHigh X / m := by gcongr
  rw [NX, sub_nonneg]
  exact Int.floor_le_floor h

/-! ## §33.2  The normalised band predicate -/

/-- The normalised band predicate: `t = m/X` admits at least `k` band multiples iff there are
`k` consecutive integers `n, …, n+k−1` with `A < n m` and `(n+k−1) m ≤ Z`. -/
def MultAtLeast (k : ℕ) (t : ℚ) : Prop :=
  ∃ n : ℤ, 7 < 10 * (n : ℚ) * t ∧ 10 * ((n : ℚ) + (k : ℚ) - 1) * t ≤ 9

/-- **`NX_ge_iff_raw`.**  `KERNEL-PROVED`.  `N_X(m) ≥ k` iff `k` consecutive multiples of `m`
lie in the band. -/
theorem NX_ge_iff_raw (X : ℚ) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (k : ℤ) ≤ NX X m ↔
      ∃ n : ℤ, bandLow X < (n : ℚ) * m ∧ ((n : ℚ) + (k : ℚ) - 1) * m ≤ bandHigh X := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  constructor
  · intro h
    refine ⟨⌊bandLow X / m⌋ + 1, ?_, ?_⟩
    · have h1 : bandLow X / m < ((⌊bandLow X / m⌋ : ℚ)) + 1 := Int.lt_floor_add_one _
      rw [div_lt_iff₀ hmQ] at h1
      push_cast
      linarith
    · have h2 : (⌊bandLow X / m⌋ + (k : ℤ)) ≤ ⌊bandHigh X / m⌋ := by
        rw [NX] at h; omega
      have h3 : (((⌊bandLow X / m⌋ + (k : ℤ)) : ℤ) : ℚ) ≤ bandHigh X / m := Int.le_floor.1 h2
      rw [le_div_iff₀ hmQ] at h3
      push_cast at h3 ⊢
      linarith
  · rintro ⟨n, h1, h2⟩
    rw [← div_lt_iff₀ hmQ] at h1
    rw [← le_div_iff₀ hmQ] at h2
    have hlt : ⌊bandLow X / m⌋ < n := Int.floor_lt.2 h1
    have hle : n + (k : ℤ) - 1 ≤ ⌊bandHigh X / m⌋ := by
      refine Int.le_floor.2 ?_
      push_cast
      linarith
    rw [NX]
    omega

/-- **`NX_ge_iff`.**  `KERNEL-PROVED`.  The normalised form: with `t = m/X`,

    N_X(m) ≥ k  ↔  MultAtLeast k t. -/
theorem NX_ge_iff (X : ℚ) (hX : 0 < X) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (k : ℤ) ≤ NX X m ↔ MultAtLeast k ((m : ℚ) / X) := by
  rw [NX_ge_iff_raw X hm k]
  constructor
  · rintro ⟨n, h1, h2⟩
    refine ⟨n, ?_, ?_⟩
    · rw [show 10 * (n : ℚ) * ((m : ℚ) / X) = (10 * (n : ℚ) * m) / X by ring, lt_div_iff₀ hX]
      unfold bandLow at h1; linarith
    · rw [show 10 * ((n : ℚ) + (k : ℚ) - 1) * ((m : ℚ) / X)
            = (10 * (((n : ℚ) + (k : ℚ) - 1) * m)) / X by ring, div_le_iff₀ hX]
      unfold bandHigh at h2; linarith
  · rintro ⟨n, h1, h2⟩
    rw [show 10 * (n : ℚ) * ((m : ℚ) / X) = (10 * (n : ℚ) * m) / X by ring, lt_div_iff₀ hX] at h1
    rw [show 10 * ((n : ℚ) + (k : ℚ) - 1) * ((m : ℚ) / X)
          = (10 * (((n : ℚ) + (k : ℚ) - 1) * m)) / X by ring, div_le_iff₀ hX] at h2
    exact ⟨n, by unfold bandLow; linarith, by unfold bandHigh; linarith⟩

/-- **`multAtLeast_mono`.**  `KERNEL-PROVED`.  More multiples implies fewer. -/
theorem multAtLeast_mono {k : ℕ} {t : ℚ} (ht : 0 < t) (h : MultAtLeast (k + 1) t) :
    MultAtLeast k t := by
  obtain ⟨n, h1, h2⟩ := h
  refine ⟨n, h1, ?_⟩
  push_cast at h2
  nlinarith

/-- **`multAtLeast_le`.**  `KERNEL-PROVED`.  Monotonicity in `k`. -/
theorem multAtLeast_le {j k : ℕ} {t : ℚ} (ht : 0 < t) (hjk : j ≤ k) (h : MultAtLeast k t) :
    MultAtLeast j t := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst this; exact h
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact ih (by omega) (multAtLeast_mono ht h)
      · have : j = k + 1 := by omega
        subst this; exact h

/-! ## §33.3  The exact band geometry, uniformly in `k` -/

/-- The chain start `c_k = ⌊7k/2⌋ + 1`: from `n = c_k` on, the bands overlap and merge into a
single interval down to `0`. -/
def chainOf (k : ℕ) : ℕ := 7 * k / 2 + 1

/-- The first admissible index `a_k = ⌊7(k−1)/2⌋ + 1`. -/
def nminOf (k : ℕ) : ℕ := 7 * (k - 1) / 2 + 1

/-- The upper endpoint of the merged tail band. -/
def tailOf (k : ℕ) : ℚ := 9 / (10 * ((chainOf k : ℚ) + (k : ℚ) - 1))

/-- Membership in a finite union of half-open rational bands `(lo, hi]`. -/
def InBands (bs : List (ℚ × ℚ)) (t : ℚ) : Prop := ∃ p ∈ bs, p.1 < t ∧ t ≤ p.2

@[simp] theorem InBands_nil (t : ℚ) : ¬ InBands [] t := by simp [InBands]

@[simp] theorem InBands_cons (p : ℚ × ℚ) (bs : List (ℚ × ℚ)) (t : ℚ) :
    InBands (p :: bs) t ↔ (p.1 < t ∧ t ≤ p.2) ∨ InBands bs t := by
  simp [InBands]

/-- The exact band decomposition of `{t > 0 : N ≥ k}`. -/
def bandsOf (k : ℕ) : List (ℚ × ℚ) :=
  (0, tailOf k) ::
    ((List.range' (nminOf k) (chainOf k - nminOf k)).map
      fun n : ℕ => (7 / (10 * (n : ℚ)), 9 / (10 * ((n : ℚ) + (k : ℚ) - 1))))

theorem mem_bandsOf_iff (k : ℕ) (p : ℚ × ℚ) :
    p ∈ bandsOf k ↔
      p = (0, tailOf k) ∨
        ∃ n : ℕ, nminOf k ≤ n ∧ n < chainOf k ∧
          p = (7 / (10 * (n : ℚ)), 9 / (10 * ((n : ℚ) + (k : ℚ) - 1))) := by
  rw [bandsOf, List.mem_cons, List.mem_map]
  constructor
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact Or.inl rfl
    · obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hn
      exact Or.inr ⟨n, h1, by omega, rfl⟩
  · rintro (rfl | ⟨n, h1, h2, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n, List.mem_range'_1.2 ⟨h1, by omega⟩, rfl⟩

/-- The tail witness: small `t` always admits `k` consecutive band multiples. -/
theorem multAtLeast_tail {k : ℕ} {t : ℚ} (ht : 0 < t) (h : 10 * (k : ℚ) * t ≤ 2) :
    MultAtLeast k t := by
  refine ⟨⌊7 / (10 * t)⌋ + 1, ?_, ?_⟩
  · have h1 : (7 : ℚ) / (10 * t) < (⌊7 / (10 * t)⌋ : ℚ) + 1 := Int.lt_floor_add_one _
    have h10 : (0 : ℚ) < 10 * t := by linarith
    rw [div_lt_iff₀ h10] at h1
    push_cast; nlinarith
  · have h2 : ((⌊7 / (10 * t)⌋ : ℚ)) ≤ 7 / (10 * t) := Int.floor_le _
    have h10 : (0 : ℚ) < 10 * t := by linarith
    rw [le_div_iff₀ h10] at h2
    push_cast; nlinarith

theorem chain_gt (k : ℕ) : 35 * k < 10 * chainOf k := by unfold chainOf; omega

theorem one_le_chainOf (k : ℕ) : 1 ≤ chainOf k := by unfold chainOf; omega

/-- **`multAtLeast_iff`.**  `KERNEL-PROVED`.  The exact rational band geometry, for every
multiplicity `k ≥ 1`:

    N ≥ k   ↔   t ∈ (0, 9/(10(c_k+k−1))] ∪ ⋃_{n=a_k}^{c_k−1} (7/(10n), 9/(10(n+k−1))]. -/
theorem multAtLeast_iff (k : ℕ) (hk : 1 ≤ k) (t : ℚ) (ht : 0 < t) :
    MultAtLeast k t ↔ InBands (bandsOf k) t := by
  have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  constructor
  · rintro ⟨n, h1, h2⟩
    have hn0 : 0 < n := by
      by_contra hc
      push_neg at hc
      have : ((n : ℚ)) ≤ 0 := by exact_mod_cast hc
      nlinarith
    have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn0
    have hkey : 7 * ((n : ℚ) + (k : ℚ) - 1) < 9 * (n : ℚ) := by nlinarith
    have hkeyZ : 7 * (n + (k : ℤ) - 1) < 9 * n := by exact_mod_cast hkey
    have hnmin : (nminOf k : ℤ) ≤ n := by unfold nminOf; omega
    by_cases hc : (chainOf k : ℤ) ≤ n
    · refine ⟨(0, tailOf k), (mem_bandsOf_iff k _).2 (Or.inl rfl), ht, ?_⟩
      have hcQ : ((chainOf k : ℚ)) ≤ (n : ℚ) := by exact_mod_cast hc
      have hcpos : (0 : ℚ) < 10 * ((chainOf k : ℚ) + (k : ℚ) - 1) := by
        have h1' : (1 : ℚ) ≤ (chainOf k : ℚ) := by exact_mod_cast one_le_chainOf k
        linarith
      show t ≤ tailOf k
      rw [tailOf, le_div_iff₀ hcpos]
      nlinarith
    · push_neg at hc
      have hcast : ((n.toNat : ℚ)) = (n : ℚ) := by
        have h' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0.le
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h'
      refine ⟨(7 / (10 * (n.toNat : ℚ)), 9 / (10 * ((n.toNat : ℚ) + (k : ℚ) - 1))),
        (mem_bandsOf_iff k _).2 (Or.inr ⟨n.toNat, by omega, by omega, rfl⟩), ?_, ?_⟩
      · show 7 / (10 * (n.toNat : ℚ)) < t
        rw [hcast, div_lt_iff₀ (by linarith : (0 : ℚ) < 10 * (n : ℚ))]
        linarith
      · show t ≤ 9 / (10 * ((n.toNat : ℚ) + (k : ℚ) - 1))
        rw [hcast, le_div_iff₀ (by linarith : (0 : ℚ) < 10 * ((n : ℚ) + (k : ℚ) - 1))]
        linarith
  · rintro ⟨p, hp, hlo, hhi⟩
    rcases (mem_bandsOf_iff k p).1 hp with rfl | ⟨n, hn1, hn2, rfl⟩
    · -- the merged tail band
      simp only at hhi
      rcases le_or_gt (10 * (k : ℚ) * t) 2 with h | h
      · exact multAtLeast_tail ht h
      · refine ⟨(chainOf k : ℤ), ?_, ?_⟩
        · have hq : (35 : ℚ) * (k : ℚ) < 10 * (chainOf k : ℚ) := by
            exact_mod_cast chain_gt k
          push_cast
          nlinarith
        · have hcpos : (0 : ℚ) < 10 * ((chainOf k : ℚ) + (k : ℚ) - 1) := by
            have h1' : (1 : ℚ) ≤ (chainOf k : ℚ) := by exact_mod_cast one_le_chainOf k
            linarith
          rw [tailOf, le_div_iff₀ hcpos] at hhi
          push_cast
          linarith
    · simp only at hlo hhi
      have hnpos : 0 < n := by
        have : 1 ≤ nminOf k := by unfold nminOf; omega
        omega
      have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hnpos
      refine ⟨(n : ℤ), ?_, ?_⟩
      · rw [div_lt_iff₀ (by linarith : (0 : ℚ) < 10 * (n : ℚ))] at hlo
        push_cast
        linarith
      · rw [le_div_iff₀ (by linarith : (0 : ℚ) < 10 * ((n : ℚ) + (k : ℚ) - 1))] at hhi
        push_cast
        linarith

/-! ## §33.4  The explicit bands for `k = 1, …, 7` -/

theorem bandsOf_one : bandsOf 1 = [(0, 9/40), (7/10, 9/10), (7/20, 9/20), (7/30, 3/10)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

theorem bandsOf_two :
    bandsOf 2 = [(0, 1/10), (7/40, 9/50), (7/50, 3/20), (7/60, 9/70), (1/10, 9/80)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

theorem bandsOf_three :
    bandsOf 3 = [(0, 9/130), (7/80, 9/100), (7/90, 9/110), (7/100, 3/40)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

theorem bandsOf_four :
    bandsOf 4 = [(0, 1/20), (7/110, 9/140), (7/120, 3/50), (7/130, 9/160), (1/20, 9/170)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

theorem bandsOf_five :
    bandsOf 5 = [(0, 9/220), (7/150, 9/190), (7/160, 9/200), (7/170, 3/70)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

theorem bandsOf_six :
    bandsOf 6 = [(0, 1/30), (7/180, 9/230), (7/190, 3/80), (7/200, 9/250), (1/30, 9/260)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

/-- **`bandsOf_seven`.**  `KERNEL-PROVED`.  The current survivor region, exactly as declared:

    Ω_{≥7} = (0, 9/310] ∪ (7/240, 3/100] ∪ (7/230, 9/290] ∪ (7/220, 9/280]. -/
theorem bandsOf_seven :
    bandsOf 7 = [(0, 9/310), (7/220, 9/280), (7/230, 9/290), (7/240, 3/100)] := by
  norm_num [bandsOf, chainOf, nminOf, tailOf, List.range']

/-! ## §33.5  Shells -/

/-- The exact shell `Ω_{=k}`: at least `k` band multiples and not `k+1`. -/
def ShellEq (k : ℕ) (t : ℚ) : Prop := MultAtLeast k t ∧ ¬ MultAtLeast (k + 1) t

/-- **`NX_eq_iff`.**  `KERNEL-PROVED`.  `N_X(m) = k` iff the normalised `t = m/X` lies in the
shell `Ω_{=k}`. -/
theorem NX_eq_iff (X : ℚ) (hX : 0 < X) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    NX X m = (k : ℤ) ↔ ShellEq k ((m : ℚ) / X) := by
  have h1 := NX_ge_iff X hX hm k
  have h2 := NX_ge_iff X hX hm (k + 1)
  constructor
  · intro h
    refine ⟨h1.1 (by omega), fun hcon => ?_⟩
    have := h2.2 hcon
    push_cast at this
    omega
  · rintro ⟨ha, hb⟩
    have hge := h1.2 ha
    have hlt : ¬ ((k : ℤ) + 1 ≤ NX X m) := by
      intro hcon
      exact hb (h2.1 (by push_cast; omega))
    omega

/-- **`shellEq_disjoint`.**  `KERNEL-PROVED`.  Distinct shells are disjoint. -/
theorem shellEq_disjoint {j k : ℕ} {t : ℚ} (ht : 0 < t) (hjk : j < k)
    (hj : ShellEq j t) (hk : ShellEq k t) : False :=
  hj.2 (multAtLeast_le ht (by omega) hk.1)

/-- **`shellOne_bands`.**  `KERNEL-PROVED`.  The exactly-one-multiple owner `Ω_{=1}` is the
union of exactly **seven** disjoint normalised bands. -/
theorem shellOne_bands (t : ℚ) (ht : 0 < t) :
    ShellEq 1 t ↔ InBands [(9/80, 7/60), (9/70, 7/50), (3/20, 7/40), (9/50, 9/40),
      (7/30, 3/10), (7/20, 9/20), (7/10, 9/10)] t := by
  rw [ShellEq, multAtLeast_iff 1 (by norm_num) t ht, multAtLeast_iff 2 (by norm_num) t ht,
    bandsOf_one, bandsOf_two]
  simp only [InBands_cons, InBands_nil, or_false]
  norm_num only
  constructor
  · rintro ⟨h, hn⟩
    have n1 : ¬ ((0 : ℚ) < t ∧ t ≤ 1/10) := fun hh => hn (Or.inl hh)
    have n2 : ¬ ((7/40 : ℚ) < t ∧ t ≤ 9/50) := fun hh => hn (Or.inr (Or.inl hh))
    have n3 : ¬ ((7/50 : ℚ) < t ∧ t ≤ 3/20) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
    have n4 : ¬ ((7/60 : ℚ) < t ∧ t ≤ 9/70) :=
      fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
    have n5 : ¬ ((1/10 : ℚ) < t ∧ t ≤ 9/80) :=
      fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr hh))))
    rcases h with h | h | h | h
    · rcases le_or_gt t (9/80) with hc | hc
      · rcases le_or_gt t (1/10) with hd | hd
        · exact (n1 ⟨ht, hd⟩).elim
        · exact (n5 ⟨hd, hc⟩).elim
      · rcases le_or_gt t (7/60) with hd | hd
        · exact Or.inl ⟨by linarith, by linarith⟩
        · rcases le_or_gt t (9/70) with he | he
          · exact (n4 ⟨hd, he⟩).elim
          · rcases le_or_gt t (7/50) with hf | hf
            · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
            · rcases le_or_gt t (3/20) with hg | hg
              · exact (n3 ⟨hf, hg⟩).elim
              · rcases le_or_gt t (7/40) with hi | hi
                · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
                · rcases le_or_gt t (9/50) with hj | hj
                  · exact (n2 ⟨hi, hj⟩).elim
                  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · intro h
    constructor
    · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    · rintro (⟨ha2, hb2⟩ | ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩) <;>
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        linarith

/-! ## §33.6  Numerical shell closures: certificates, never theorems -/

/-- A numerical certificate for a shell contribution: the shell index, the claimed relative
size and a strict bound.  Inhabiting this structure *is* the certificate: nothing in this file
proves any analytic shell estimate, and no axiom is introduced for one. -/
structure ShellNumericalCertificate where
  /-- The shell index (or `0` for an aggregate of shells). -/
  shell : ℕ
  /-- The claimed relative contribution `|S|/B_X`. -/
  value : ℚ
  /-- The certified strict upper bound. -/
  bound : ℚ
  /-- The certificate hypothesis. -/
  value_lt : value < bound

/-- **`shellCertificate_not_proved`.**  `KERNEL-PROVED`.  Firewall: the certificate type is
inhabited for every shell and every bound, so possessing one proves nothing analytic. -/
theorem shellCertificate_not_proved (s : ℕ) (bound : ℚ) :
    ∃ C : ShellNumericalCertificate, C.shell = s ∧ C.bound = bound :=
  ⟨⟨s, bound - 1, bound, by linarith⟩, rfl, rfl⟩

/-- The declared (certificate-backed) numerical value for the `N = 1` owner: `2.4e-8`. -/
def shellOneCharge : ℚ := 24 / 10 ^ 9

/-- The declared (certificate-backed) numerical value for the `N = 2..5` owner: `2.16e-8`. -/
def shellTwoToFiveCharge : ℚ := 216 / 10 ^ 10

/-- **`shellCharges_exact`.**  `KERNEL-PROVED` (exact rational arithmetic only). -/
theorem shellCharges_exact :
    shellOneCharge = 24 / 10 ^ 9 ∧ shellTwoToFiveCharge = 216 / 10 ^ 10 := ⟨rfl, rfl⟩

end Effectivity
end Erdos287
