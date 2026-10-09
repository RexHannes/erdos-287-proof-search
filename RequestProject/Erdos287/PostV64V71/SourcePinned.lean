import RequestProject.Erdos287.PostQSigma.HardCore

/-!
# Erdős #287 — V67 direct selected-mass / pinned normalisation

**Status: BANK (LEAN PROVED), with one REPAIR.**

Literal raw-source dictionary (PostQSigma): `W = lcm(a,…,M)`, `T = ∑_{n∈[a,M]} W/n - W`,
`B(E) = ∑_{n∈E} W/n`, `X(E) = B(E) - T`, for an omission set `E ⊆ (a, M)`.

Pinned language: the selected set `A = [a, M] \ E`; a residual denominator `D` with
`n ∣ D` for every `n ∈ A` and `D ∣ W`; the pinning cofactor `P = W / D`; the integer selected
mass `Y(A) = ∑_{n∈A} D/n`.

* `pinned_selected_mass` — **`X(E) = P · (D - Y(A))`** (exact; no prime-row independence, no
  random-residue heuristic, no modulo-`W` surrogate);
* `pinned_selected_mass_iff` — `X(E) = 0 ↔ Y(A) = D`;
* `pinned_mass_bounds` — `0 < Y(A) < 2D` when `H(a,M) < 2`;
* `pinned_W_dvd_iff` — `W ∣ X(E) ↔ Y(A) = D` (given `0 < Y < 2D`);
* `pinned_D_dvd_iff_of_coprime` — `D ∣ X(E) ↔ X(E) = 0` **when `gcd(P, D) = 1`**.

**REPAIR.**  The literal candidate equivalence "`X(E) = 0 ↔ D ∣ X(E)`" is not valid in the stated
generality: the algebraic shape `X = P(D - Y)` admits `P = D = 2`, `Y = 1` (`0 < Y < 2D`,
`D ∣ X`, `Y ≠ D`) — `pinned_D_dvd_counterfixture`.  The correct third equivalent is `W ∣ X(E)`
(i.e. `PD ∣ X(E)`), or `D ∣ X(E)` under `gcd(P, D) = 1`.
-/

open scoped BigOperators

namespace Erdos287.PostV64V71

open Erdos287.ExactSource Erdos287.PostQSigma

/-- The selected set `A = [a, M] \ E`. -/
def Asel (a M : ℕ) (E : Finset ℕ) : Finset ℕ := Finset.Icc a M \ E

/-- The integer selected mass `Y(A) = ∑_{n∈A} D/n`. -/
def Ymass (D : ℕ) (A : Finset ℕ) : ℕ := ∑ n ∈ A, D / n

/-- **V67 pinned identity**: `X(E) = (W/D) · (D - Y(A))`. -/
theorem pinned_selected_mass {a M D : ℕ} {E : Finset ℕ} (hE : E ⊆ Finset.Ioo a M)
    (hD : ∀ n ∈ Asel a M E, n ∣ D) (hDW : D ∣ W a M ∅) :
    Xd a M E = ((W a M ∅ / D : ℕ) : ℤ) * ((D : ℤ) - Ymass D (Asel a M E)) := by
  set W0 := W a M ∅
  set P := W0 / D
  have hWPD : W0 = P * D := (Nat.div_mul_cancel hDW).symm
  have hEsub : E ⊆ Finset.Icc a M := fun n hn => Finset.Ioo_subset_Icc_self (hE hn)
  -- `∑_{n∈A} W/n = P · Y`
  have hsumA : ∑ n ∈ Asel a M E, W0 / n = P * Ymass D (Asel a M E) := by
    unfold Ymass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hWPD, Nat.mul_div_assoc P (hD n hn)]
  have hT : T a M ∅ = (∑ n ∈ Finset.Icc a M, ((W0 / n : ℕ) : ℤ)) - (W0 : ℤ) := by
    unfold T; rw [B, Finset.sdiff_empty]
  have hsplit : ∑ n ∈ Finset.Icc a M, ((W0 / n : ℕ) : ℤ) =
      ∑ n ∈ Asel a M E, ((W0 / n : ℕ) : ℤ) + ∑ n ∈ E, ((W0 / n : ℕ) : ℤ) := by
    unfold Asel; rw [Finset.sum_sdiff hEsub]
  have hA : ∑ n ∈ Asel a M E, ((W0 / n : ℕ) : ℤ) = (P : ℤ) * Ymass D (Asel a M E) := by
    rw [← Nat.cast_sum, hsumA]; push_cast; ring
  have hW0 : (W0 : ℤ) = (P : ℤ) * D := by exact_mod_cast hWPD
  unfold Xd
  rw [cast_Bm, hT, hsplit, hA, hW0]
  ring

/-- `X(E) = 0 ↔ Y(A) = D` (for `a > 0`, so `W ≠ 0`). -/
theorem pinned_selected_mass_iff {a M D : ℕ} {E : Finset ℕ} (ha : 0 < a)
    (hE : E ⊆ Finset.Ioo a M) (hD : ∀ n ∈ Asel a M E, n ∣ D) (hDW : D ∣ W a M ∅) :
    Xd a M E = 0 ↔ Ymass D (Asel a M E) = D := by
  rw [pinned_selected_mass hE hD hDW]
  have hW0 : W a M ∅ ≠ 0 := W_ne_zero ha
  have hD0 : D ≠ 0 := fun h => hW0 (Nat.eq_zero_of_zero_dvd (h ▸ hDW))
  have hP : W a M ∅ / D ≠ 0 := by
    intro h
    rw [Nat.div_eq_zero_iff] at h
    rcases h with h | h
    · exact hD0 h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hW0) hDW) (not_le.2 h)
  rw [mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd (by exact_mod_cast h) hP
    · exact_mod_cast h.symm
  · intro h; right; exact_mod_cast h.symm

/-- `0 < Y(A) < 2D` when `H(a,M) < 2` (and `0 < a ≤ M`, `D > 0`). -/
theorem pinned_mass_bounds {a M D : ℕ} {E : Finset ℕ} (ha : 0 < a) (haM : a ≤ M)
    (hE : E ⊆ Finset.Ioo a M) (hD : ∀ n ∈ Asel a M E, n ∣ D) (hD0 : 0 < D)
    (hH : Hm a M < 2) : 0 < Ymass D (Asel a M E) ∧ Ymass D (Asel a M E) < 2 * D := by
  have haA : a ∈ Asel a M E := by
    unfold Asel
    refine Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, haM⟩, fun h => ?_⟩
    have := Finset.mem_Ioo.1 (hE h); omega
  have hpos : ∀ n ∈ Asel a M E, 0 < n := fun n hn => by
    have := Finset.mem_Icc.1 (Finset.mem_sdiff.1 hn).1; omega
  constructor
  · unfold Ymass
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) haA)
    exact Nat.div_pos (Nat.le_of_dvd hD0 (hD a haA)) ha
  · have hcast : (Ymass D (Asel a M E) : ℚ) = D * ∑ n ∈ Asel a M E, (1 : ℚ) / n := by
      unfold Ymass; push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Nat.cast_div (hD n hn) (by have := hpos n hn; positivity)]
      ring
    have hle : ∑ n ∈ Asel a M E, (1 : ℚ) / n ≤ Hm a M := by
      unfold Hm Asel
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        fun n _ _ => by positivity
    have : (Ymass D (Asel a M E) : ℚ) < 2 * D := by
      rw [hcast]
      have hD0' : (0 : ℚ) < D := by exact_mod_cast hD0
      nlinarith
    exact_mod_cast this

/-- `D ∣ D - Y` with `0 < Y < 2D` forces `Y = D`. -/
theorem eq_of_dvd_sub {D Y : ℕ} (hY : 0 < Y ∧ Y < 2 * D) (h : (D : ℤ) ∣ (D : ℤ) - Y) :
    Y = D := by
  obtain ⟨c, hc⟩ := h
  have hD0 : (0 : ℤ) < D := by have := hY.2; omega
  have hlt1 : (D : ℤ) - Y < D := by have := hY.1; omega
  have hlt2 : -(D : ℤ) < D - Y := by have := hY.2; omega
  have hc0 : c = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (D : ℤ) * c ≤ -D := by nlinarith
      omega
    · have : (D : ℤ) ≤ D * c := by nlinarith
      omega
  rw [hc0, mul_zero] at hc
  omega

/-- `W ∣ X(E) ↔ Y(A) = D`, given `0 < Y(A) < 2D`. -/
theorem pinned_W_dvd_iff {a M D : ℕ} {E : Finset ℕ} (ha : 0 < a)
    (hE : E ⊆ Finset.Ioo a M) (hD : ∀ n ∈ Asel a M E, n ∣ D) (hDW : D ∣ W a M ∅)
    (hY : 0 < Ymass D (Asel a M E) ∧ Ymass D (Asel a M E) < 2 * D) :
    ((W a M ∅ : ℕ) : ℤ) ∣ Xd a M E ↔ Ymass D (Asel a M E) = D := by
  rw [pinned_selected_mass hE hD hDW]
  set P := W a M ∅ / D
  set Y := Ymass D (Asel a M E)
  have hW0 : W a M ∅ ≠ 0 := W_ne_zero ha
  have hWPD : W a M ∅ = P * D := (Nat.div_mul_cancel hDW).symm
  have hP0 : (P : ℤ) ≠ 0 := by
    intro h; apply hW0; rw [hWPD]; simp only [Nat.cast_eq_zero] at h; rw [h, zero_mul]
  have hWZ : ((W a M ∅ : ℕ) : ℤ) = (P : ℤ) * D := by exact_mod_cast hWPD
  rw [hWZ]
  constructor
  · intro h
    exact eq_of_dvd_sub hY ((mul_dvd_mul_iff_left hP0).1 h)
  · intro h; rw [h, sub_self, mul_zero]; exact dvd_zero _

/-- `D ∣ X(E) ↔ X(E) = 0` when `gcd(W/D, D) = 1` and `0 < Y(A) < 2D`. -/
theorem pinned_D_dvd_iff_of_coprime {a M D : ℕ} {E : Finset ℕ} (ha : 0 < a)
    (hE : E ⊆ Finset.Ioo a M) (hD : ∀ n ∈ Asel a M E, n ∣ D) (hDW : D ∣ W a M ∅)
    (hcop : Nat.Coprime (W a M ∅ / D) D)
    (hY : 0 < Ymass D (Asel a M E) ∧ Ymass D (Asel a M E) < 2 * D) :
    (D : ℤ) ∣ Xd a M E ↔ Xd a M E = 0 := by
  rw [pinned_selected_mass_iff ha hE hD hDW]
  constructor
  · intro h
    rw [pinned_selected_mass hE hD hDW] at h
    have hcopZ : IsCoprime (D : ℤ) ((W a M ∅ / D : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hcop.symm
    exact eq_of_dvd_sub hY (hcopZ.dvd_of_dvd_mul_left h)
  · intro h
    rw [pinned_selected_mass hE hD hDW, h, sub_self, mul_zero]
    exact dvd_zero _

/-- **REPAIR fixture**: the shape `X = P (D - Y)` with `0 < Y < 2D` does not force
`D ∣ X ⇒ Y = D` without coprimality (`P = D = 2`, `Y = 1`). -/
theorem pinned_D_dvd_counterfixture :
    ∃ P D Y : ℕ, 0 < Y ∧ Y < 2 * D ∧ (D : ℤ) ∣ (P : ℤ) * ((D : ℤ) - Y) ∧ Y ≠ D :=
  ⟨2, 2, 1, by norm_num, by norm_num, ⟨1, by norm_num⟩, by norm_num⟩

end Erdos287.PostV64V71
