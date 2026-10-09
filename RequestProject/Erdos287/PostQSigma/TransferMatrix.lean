import RequestProject.Erdos287.PostQSigma.PathCount

/-!
# Erdős #287 — post-`Q_Σ` bank, §29: the hard-core transfer matrix

**Status: BANK (proved in Lean), exact algebra only.**  No local contraction / spectral claim is
made, and nothing here is claimed to prove the global theorem.

Over any commutative ring `R` (e.g. `ℂ` or a cyclotomic ring, where `u_i = e_W(r·W/n_i)`):

* `Zw u n = ∑_{S ⊆ {0,…,n-1} independent} ∏_{i∈S} u_i` — weighted independence polynomial of the
  path (this is the twisted sum `Z(r)` of the Fourier filter, after relabelling the path);
* `Zw_succ_succ` — `Z_{j} = Z_{j-1} + u_j Z_{j-2}`;
* `tmat u = !![1, u; 1, 0]`, `tmat_mulVec` and `transfer_matrix_product` — the matrix-product
  representation `(Z_{n+1}, Z_n) = A(u_n)⋯A(u_0)·(1,1)`;
* `tmat_mul_tmat` — the exact two-step product `A(u)A(v) = !![1+u, v; 1, v]`, `tmat_det`;
* `Zw_one` — at `u ≡ 1` the polynomial is the path count `indepCount`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma.Transfer

open Erdos287.ExactSource

open Classical in
/-- Weighted independence polynomial of the path `0 — 1 — ⋯ — (n-1)`. -/
noncomputable def Zw {R : Type*} [CommRing R] (u : ℕ → R) (n : ℕ) : R :=
  ∑ S ∈ (Finset.range n).powerset.filter Indep, ∏ i ∈ S, u i

open Classical in
lemma filter_not_mem (n : ℕ) :
    ((Finset.range (n + 2)).powerset.filter Indep).filter (fun E => ¬ (n + 1 ∈ E)) =
      (Finset.range (n + 1)).powerset.filter Indep := by
  ext E
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hE, hI⟩, hn⟩
    refine ⟨fun x hx => ?_, hI⟩
    have := Finset.mem_range.1 (hE hx)
    have : x ≠ n + 1 := fun h => hn (h ▸ hx)
    exact Finset.mem_range.2 (by omega)
  · rintro ⟨hE, hI⟩
    refine ⟨⟨hE.trans (Finset.range_subset_range.2 (by omega)), hI⟩, fun h => ?_⟩
    have := Finset.mem_range.1 (hE h); omega

open Classical in
lemma filter_mem (n : ℕ) :
    ((Finset.range (n + 2)).powerset.filter Indep).filter (fun E => n + 1 ∈ E) =
      ((Finset.range n).powerset.filter Indep).image (insert (n + 1)) := by
  ext E
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨hE, hI⟩, hn⟩
    refine ⟨E.erase (n + 1), ⟨fun x hx => ?_, fun x hx hx1 => hI x (Finset.mem_of_mem_erase hx)
      (Finset.mem_of_mem_erase hx1)⟩, Finset.insert_erase hn⟩
    have hxE := Finset.mem_of_mem_erase hx
    have hx1 := Finset.ne_of_mem_erase hx
    have := Finset.mem_range.1 (hE hxE)
    have hxn : x ≠ n := fun h => hI x hxE (h ▸ hn)
    exact Finset.mem_range.2 (by omega)
  · rintro ⟨F, ⟨hF, hI⟩, rfl⟩
    refine ⟨⟨fun x hx => ?_, fun x hx hx1 => ?_⟩, Finset.mem_insert_self _ _⟩
    · rcases Finset.mem_insert.1 hx with h | h
      · exact Finset.mem_range.2 (by omega)
      · have := Finset.mem_range.1 (hF h); exact Finset.mem_range.2 (by omega)
    · rcases Finset.mem_insert.1 hx with h | h
      · subst h
        rcases Finset.mem_insert.1 hx1 with h' | h'
        · omega
        · have := Finset.mem_range.1 (hF h'); omega
      · have hxn := Finset.mem_range.1 (hF h)
        rcases Finset.mem_insert.1 hx1 with h' | h'
        · omega
        · exact hI x h h'

/-- **Independent-set recurrence** `Z_{n+2} = Z_{n+1} + u_{n+1} Z_n`. -/
theorem Zw_succ_succ {R : Type*} [CommRing R] (u : ℕ → R) (n : ℕ) :
    Zw u (n + 2) = Zw u (n + 1) + u (n + 1) * Zw u n := by
  classical
  unfold Zw
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun E => n + 1 ∈ E), filter_mem, filter_not_mem,
    add_comm]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun F hF => ?_)
    have hF' := (Finset.mem_filter.1 hF).1
    rw [Finset.mem_powerset] at hF'
    have : n + 1 ∉ F := fun h => by have := Finset.mem_range.1 (hF' h); omega
    rw [Finset.prod_insert this]
  · intro F hF G hG h
    have hF' := (Finset.mem_filter.1 (Finset.mem_coe.1 hF)).1
    have hG' := (Finset.mem_filter.1 (Finset.mem_coe.1 hG)).1
    rw [Finset.mem_powerset] at hF' hG'
    have nF : n + 1 ∉ F := fun h => by have := Finset.mem_range.1 (hF' h); omega
    have nG : n + 1 ∉ G := fun h => by have := Finset.mem_range.1 (hG' h); omega
    have := congrArg (fun E => E.erase (n + 1)) h
    simpa [Finset.erase_insert nF, Finset.erase_insert nG] using this

theorem Zw_zero {R : Type*} [CommRing R] (u : ℕ → R) : Zw u 0 = 1 := by
  classical
  unfold Zw
  rw [Finset.range_zero, Finset.powerset_empty, Finset.filter_singleton]
  simp [Indep]

theorem Zw_one' {R : Type*} [CommRing R] (u : ℕ → R) : Zw u 1 = 1 + u 0 := by
  classical
  unfold Zw
  have : (Finset.range 1).powerset.filter Indep = (Finset.range 1).powerset :=
    Finset.filter_true_of_mem (fun E hE x hx hx1 => by
      have h := Finset.mem_powerset.1 hE
      have a := Finset.mem_range.1 (h hx); have b := Finset.mem_range.1 (h hx1); omega)
  rw [this, Finset.range_one, show ({0} : Finset ℕ) = insert 0 ∅ from rfl,
    Finset.sum_powerset_insert (by simp)]
  simp

/-- The hard-core transfer matrix `A(u) = [[1,u],[1,0]]`. -/
def tmat {R : Type*} [CommRing R] (u : R) : Matrix (Fin 2) (Fin 2) R := !![1, u; 1, 0]

/-- The state vector `(Z_{n+1}, Z_n)`. -/
noncomputable def zvec {R : Type*} [CommRing R] (u : ℕ → R) (n : ℕ) : Fin 2 → R :=
  ![Zw u (n + 1), Zw u n]

/-- One transfer step. -/
theorem tmat_mulVec {R : Type*} [CommRing R] (u : ℕ → R) (n : ℕ) :
    (tmat (u (n + 1))).mulVec (zvec u n) = zvec u (n + 1) := by
  ext i
  fin_cases i
  · simp [tmat, zvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Zw_succ_succ]
  · simp [tmat, zvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The ordered product `A(u_n) ⋯ A(u_0)`. -/
def tprod {R : Type*} [CommRing R] (u : ℕ → R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => tmat (u 0)
  | n + 1 => tmat (u (n + 1)) * tprod u n

/-- **Matrix-product representation** `(Z_{n+1}, Z_n) = A(u_n)⋯A(u_0)·(1,1)`. -/
theorem transfer_matrix_product {R : Type*} [CommRing R] (u : ℕ → R) (n : ℕ) :
    zvec u n = (tprod u n).mulVec ![1, 1] := by
  induction n with
  | zero =>
    ext i; fin_cases i
    · simp [zvec, tprod, tmat, Zw_one', Zw_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [zvec, tprod, tmat, Zw_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | succ n ih =>
    rw [tprod, ← Matrix.mulVec_mulVec, ← ih, tmat_mulVec]

/-- The exact two-step product. -/
theorem tmat_mul_tmat {R : Type*} [CommRing R] (u v : R) :
    tmat u * tmat v = !![1 + u, v; 1, v] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tmat, Matrix.mul_apply, Fin.sum_univ_two]

theorem tmat_det {R : Type*} [CommRing R] (u : R) : (tmat u).det = -u := by
  simp [tmat, Matrix.det_fin_two]

/-- At `u ≡ 1` the weighted polynomial is the path count. -/
theorem Zw_one (n : ℕ) : Zw (fun _ => (1 : ℤ)) n = indepCount n := by
  classical
  unfold Zw indepCount
  simp

end Erdos287.PostQSigma.Transfer
