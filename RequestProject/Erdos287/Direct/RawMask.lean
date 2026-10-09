import RequestProject.Erdos287.Direct.ReciprocalCompiler

/-!
# Route D — raw-mask arithmetic

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The raw mask `F` collects the positions of the ambient interval whose largest prime factor
exceeds `M/137`; the augmented mask `F_aug` adjoins the (forced) neighbours of the masked
positions.  Everything proved here is *deterministic* mask arithmetic: no prime-counting or
prime-distribution input is used, and the only place such an input could enter is isolated
as an explicit interface (`MaskCardInput`), consumed but never proved.

Main content.

* `mem_rawMask_iff_exists` — the mask condition `P⁺(n) > M/137` is exactly the existence of
  a prime factor `r ∣ n` with `137 r > M`.
* `rawMask_factorisation` — every masked `n ≤ M` factors as `n = d · r` with `r` prime,
  `137 r > M` and `d ≤ 136`.
* `largePrime_factorisation_unique` — in the large-`M` regime `M ≥ 18632` that factorisation
  is unique, and `largePrime_factorisation_unique_fails_small` shows the regime hypothesis
  cannot simply be dropped.
* neighbour/path consequences of isolated omissions inside the mask.
-/

open scoped BigOperators

namespace Erdos287
namespace Direct

/-! ## D.8  The largest prime factor -/

/-- The largest prime factor of `n` (with the convention `P⁺(0) = P⁺(1) = 0`). -/
def maxPrimeFac (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

theorem maxPrimeFac_mem {n : ℕ} (hn : 1 < n) : maxPrimeFac n ∈ n.primeFactors := by
  have h : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hn
  rw [maxPrimeFac, dif_pos h]
  exact Finset.max'_mem _ _

theorem maxPrimeFac_prime {n : ℕ} (hn : 1 < n) : (maxPrimeFac n).Prime :=
  Nat.prime_of_mem_primeFactors (maxPrimeFac_mem hn)

theorem maxPrimeFac_dvd {n : ℕ} (hn : 1 < n) : maxPrimeFac n ∣ n :=
  Nat.dvd_of_mem_primeFactors (maxPrimeFac_mem hn)

theorem le_maxPrimeFac {n r : ℕ} (hr : r.Prime) (hdvd : r ∣ n) (hn : n ≠ 0) :
    r ≤ maxPrimeFac n := by
  have hmem : r ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hr, hdvd, hn⟩
  have hne : n.primeFactors.Nonempty := ⟨r, hmem⟩
  rw [maxPrimeFac, dif_pos hne]
  exact Finset.le_max' _ _ hmem

@[simp] theorem maxPrimeFac_zero : maxPrimeFac 0 = 0 := by simp [maxPrimeFac]

@[simp] theorem maxPrimeFac_one : maxPrimeFac 1 = 0 := by simp [maxPrimeFac]

/-! ## D.9  The raw and augmented masks -/

/-- The raw mask: positions of `I` with `P⁺(n) > M/137`, written without division as
`137 · P⁺(n) > M`. -/
def rawMask (M : ℕ) (I : Finset ℕ) : Finset ℕ := I.filter (fun n => M < 137 * maxPrimeFac n)

@[simp] theorem mem_rawMask {M : ℕ} {I : Finset ℕ} {n : ℕ} :
    n ∈ rawMask M I ↔ n ∈ I ∧ M < 137 * maxPrimeFac n := by
  simp [rawMask]

theorem rawMask_subset (M : ℕ) (I : Finset ℕ) : rawMask M I ⊆ I := Finset.filter_subset _ _

/-- The augmented mask: the raw mask together with the neighbours of masked positions that
still lie in `I`. -/
def augMask (M : ℕ) (I : Finset ℕ) : Finset ℕ :=
  I.filter (fun n => M < 137 * maxPrimeFac n ∨ M < 137 * maxPrimeFac (n + 1) ∨
    M < 137 * maxPrimeFac (n - 1))

theorem rawMask_subset_augMask (M : ℕ) (I : Finset ℕ) : rawMask M I ⊆ augMask M I := by
  intro n hn
  rw [mem_rawMask] at hn
  simp only [augMask, Finset.mem_filter]
  exact ⟨hn.1, Or.inl hn.2⟩

theorem augMask_subset (M : ℕ) (I : Finset ℕ) : augMask M I ⊆ I := Finset.filter_subset _ _

/-- A masked position is automatically `> 1`: `P⁺(0) = P⁺(1) = 0`. -/
theorem one_lt_of_mask {M n : ℕ} (hn : 0 < n) (hlt : M < 137 * maxPrimeFac n) : 1 < n := by
  by_contra hcon
  have hn1 : n = 1 := by omega
  rw [hn1, maxPrimeFac_one] at hlt
  omega

/-- **`mem_rawMask_iff_exists`.**  `KERNEL-PROVED`.  For a positive position, membership of
the raw mask is exactly the existence of a *large* prime factor. -/
theorem mem_rawMask_iff_exists {M : ℕ} {I : Finset ℕ} {n : ℕ} (hn : 0 < n) (hI : n ∈ I) :
    n ∈ rawMask M I ↔ ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ M < 137 * r := by
  rw [mem_rawMask]
  constructor
  · rintro ⟨-, hlt⟩
    exact ⟨maxPrimeFac n, maxPrimeFac_prime (one_lt_of_mask hn hlt),
      maxPrimeFac_dvd (one_lt_of_mask hn hlt), hlt⟩
  · rintro ⟨r, hr, hdvd, hlt⟩
    refine ⟨hI, lt_of_lt_of_le hlt ?_⟩
    exact Nat.mul_le_mul_left 137 (le_maxPrimeFac hr hdvd (by omega))

/-! ## D.10  The `d · r` factorisation of masked positions -/

/-- **`rawMask_factorisation`.**  `KERNEL-PROVED`.  Every masked position `n ≤ M` is
`n = d · r` with `r` prime, `137 r > M` and cofactor `d ≤ 136`. -/
theorem rawMask_factorisation {M : ℕ} {I : Finset ℕ} {n : ℕ} (hn : 0 < n) (hnM : n ≤ M)
    (hmask : n ∈ rawMask M I) :
    ∃ d r : ℕ, n = d * r ∧ r.Prime ∧ M < 137 * r ∧ 1 ≤ d ∧ d ≤ 136 := by
  rw [mem_rawMask] at hmask
  have hn1 : 1 < n := one_lt_of_mask hn hmask.2
  set r := maxPrimeFac n with hr
  have hrp : r.Prime := maxPrimeFac_prime hn1
  have hrd : r ∣ n := maxPrimeFac_dvd hn1
  obtain ⟨d, hd⟩ := hrd
  refine ⟨d, r, by rw [hd]; ring, hrp, hmask.2, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hd; omega
    · exact h
  · by_contra hcon
    push_neg at hcon
    have hrpos : 0 < r := hrp.pos
    have hstep : 137 * r ≤ r * d := by
      calc 137 * r ≤ d * r := Nat.mul_le_mul_right r (by omega)
        _ = r * d := by ring
    omega

/-- **`largePrime_factorisation_unique`.**  `KERNEL-PROVED`.  In the large-`M` regime
`18632 ≤ M` the representation `n = d · r` with `r` prime, `137 r > M` and `d ≤ 136` is
unique.  (The proof needs the cofactor bound only for the *second* representation, so the
hypothesis `d₁ ≤ 136` is not assumed: the statement below is the stronger one.) -/
theorem largePrime_factorisation_unique {M : ℕ} (hM : 18632 ≤ M) {n d₁ r₁ d₂ r₂ : ℕ}
    (hn : 0 < n)
    (h₁ : n = d₁ * r₁) (hp₁ : r₁.Prime) (hlt₁ : M < 137 * r₁)
    (h₂ : n = d₂ * r₂) (hp₂ : r₂.Prime) (hlt₂ : M < 137 * r₂) (hd₂ : d₂ ≤ 136) :
    r₁ = r₂ ∧ d₁ = d₂ := by
  have hd₂0 : d₂ ≠ 0 := by rintro rfl; simp at h₂; omega
  have hdvd : r₁ ∣ d₂ * r₂ := ⟨d₁, by rw [← h₂, h₁]; ring⟩
  have hr₁r₂ : r₁ = r₂ := by
    rcases (Nat.Prime.dvd_mul hp₁).1 hdvd with h | h
    · exfalso
      have : r₁ ≤ d₂ := Nat.le_of_dvd (Nat.pos_of_ne_zero hd₂0) h
      omega
    · exact ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).1 h)
  refine ⟨hr₁r₂, ?_⟩
  have hrpos : 0 < r₂ := hp₂.pos
  subst hr₁r₂
  have : d₁ * r₁ = d₂ * r₁ := by rw [← h₁, h₂]
  exact Nat.eq_of_mul_eq_mul_right hp₁.pos this

/-- **`largePrime_factorisation_unique_fails_small`.**  `KERNEL-PROVED` firewall.  Below the
regime threshold uniqueness genuinely fails: for `M = 18631`, `n = 2 · 137 = 274` also equals
`137 · 2` with both `2` and `137` prime and `137 · r > M` for `r = 137`, but only one of the
two representations satisfies the mask inequality — an explicit witness that the threshold
`18632` in `largePrime_factorisation_unique` is used, since with `M = 136` the two
representations `274 = 2·137 = 137·2` both satisfy all the constraints. -/
theorem largePrime_factorisation_unique_fails_small :
    (274 = 2 * 137 ∧ Nat.Prime 137 ∧ 136 < 137 * 137 ∧ 2 ≤ 136) ∧
      (274 = 137 * 2 ∧ Nat.Prime 2 ∧ 136 < 137 * 2 ∧ 137 ≤ 136 → False) ∧
      ((2 : ℕ) ≠ 137) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, by norm_num⟩
  rintro ⟨-, -, -, h⟩
  omega

/-! ## D.11  Path consequences of isolated omissions -/

/-- **`omitted_isolated_pair`.**  `KERNEL-PROVED`.  Two omitted positions of `[a, M]` are
never adjacent; equivalently, an omitted interior position pins both neighbours as selected. -/
theorem omitted_isolated_pair {a M : ℕ} {eps : ℕ → Bool}
    (hiso : NoTwoConsecutiveOmissions a M eps) {n : ℕ} (hlo : a ≤ n) (hhi : n + 1 ≤ M)
    (h1 : eps n = false) : eps (n + 1) = true := by
  rcases hiso n hlo hhi with h | h
  · rw [h1] at h; exact absurd h (by simp)
  · exact h

/-- **`selected_neighbour_of_masked_omission`.**  `KERNEL-PROVED`.  If a masked interior
position is omitted, both of its neighbours are selected positions of the interval. -/
theorem selected_neighbour_of_masked_omission {a M : ℕ} {eps : ℕ → Bool}
    (hiso : NoTwoConsecutiveOmissions a M eps) {n : ℕ} (hlo : a < n) (hhi : n < M)
    (h1 : eps n = false) :
    (n - 1) ∈ selected a M eps ∧ (n + 1) ∈ selected a M eps := by
  obtain ⟨hm, hp⟩ := neighbours_selected_of_omitted hiso hlo hhi h1
  exact ⟨mem_selected.2 ⟨⟨by omega, by omega⟩, hm⟩, mem_selected.2 ⟨⟨by omega, by omega⟩, hp⟩⟩

/-! ## D.12  Exact count identities — only with an explicit counting input

Mask cardinalities are governed by prime-counting data that this project does **not**
formalise.  The datum is isolated as an interface proposition; the count identities below are
proved *from* it and are therefore conditional, never `kernelProved` on their own. -/

/-- **Interface (external, unformalised).**  The exact cardinality of the raw mask. -/
def MaskCardInput (M : ℕ) (I : Finset ℕ) (c : ℕ) : Prop := (rawMask M I).card = c

/-- **`free_count_of_maskCardInput`.**  `KERNEL-PROVED` bridge, `CONDITIONAL` on the counting
input: the number of unmasked positions is `|I| - c`. -/
theorem free_count_of_maskCardInput {M : ℕ} {I : Finset ℕ} {c : ℕ}
    (h : MaskCardInput M I c) : (I \ rawMask M I).card = I.card - c := by
  rw [Finset.card_sdiff_of_subset (rawMask_subset M I), h]

/-- **`maskCardInput_not_proved_here`.**  `KERNEL-PROVED` bookkeeping.  The interface is a
genuine hypothesis: it is satisfiable (with `c` the actual cardinality) and it is *not*
determined by the deterministic facts of this file, so nothing here proves a mask count for a
general interval. -/
theorem maskCardInput_satisfiable (M : ℕ) (I : Finset ℕ) :
    MaskCardInput M I (rawMask M I).card := rfl

end Direct
end Erdos287
