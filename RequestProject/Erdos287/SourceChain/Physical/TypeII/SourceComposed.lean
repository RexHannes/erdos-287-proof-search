import RequestProject.Erdos287.SourceChain.Physical.TypeII.ProviderDictionary
import RequestProject.Erdos287.SourceChain.Physical.Remainder

/-!
# Erdős #287 — the actual scalar Type-II source, composed down to Ordering-B cells

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

One source-exact identity, assembled from `ellX_tensor` (via `physCoefAtom_reassemble`),
`typeII_source_decomp` and `OBData.source_eq_T`:

* `scalarTypeII` — the scalar Type-II source of one packet:
  `Γ ∑_{1 ≤ d < K} 1[(f,d)=1] ℓ_X(d) ∑_{v < K'} (α * β)(v) 1_{v ≡ c (f)} (I_d - U_d)(v)`.
* `physCoefCut` — the constructed atom coefficient with the source cutoff `l r < K` kept.
* `physCell` — the Ordering-B cell of an atom `(J,P,χ)` at dyadic scales `L = 2^i`,
  `R = 2^{i'}` (the atom, its colouring and its coefficient are selected **before** Cauchy).
* `physUrem` — the `h_l U_r` part of the exact Type-II split.
* `scalarTypeII_eq_cells` — **exact identity**
  `scalarTypeII = ∑_{J,P,χ} ∑_{i,i' < n} T(physCell …) + physUrem` for every `K ≤ 2^n`;
  signs `(-1)^J`, box multiplicities (`atomWeight`), residues `c` mod `f`, `(A, B)`, the scalar
  `Γ` and the atom variation all appear exactly once.
* `packet_typeII_eq_cells` — the same, summed **once** over the labelled packet set `Ξ`
  (`XiAll`), with `Γ_ξ`, `f_ξ`, `c_ξ`, `A_ξ`, `B_ξ` of the actual packet: the designated pair
  `(j, ℓ)` is part of the packet index and is **not** summed again inside the atom/cell sums.
* `physCell_contract` — for an actual critical cell (`CritRegime`, `CritCell` with `N = N_n`),
  every cell coefficient obeys: `|c(l,r)| ≤ |Γ| w_{J,P}`; nonzero ⇒ `(l,r) = 1`, `(f, l r) = 1`,
  `l r < K`, `l ≤ Q = N X^{-κ}`, `r = a₂ a₃` with `a₂ ≤ S`, `a₃ ≤ R`; plus the three boxed
  range conditions.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Physical.TypeII

open Erdos287.Physical.Sieve Erdos287.Physical.Sieve.ScalarParams Erdos287.Physical.Factor

open Classical in
/-- The residue mask `1_{v ≡ c (mod f)}`. -/
noncomputable def resMask (f c v : ℕ) : ℝ := if v ≡ c [MOD f] then 1 else 0

variable (S : ScalarParams)

open Classical in
/-- **The scalar Type-II source of one packet.** -/
noncomputable def scalarTypeII (Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α β : ArithmeticFunction ℝ) : ℝ :=
  Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then
    S.ellX d * ∑ v ∈ range K', (α * β) v * (resMask f c v * (Iz A B d v - Uz d v)) else 0

/-- The constructed atom coefficient with the source cutoff `l r < K`. -/
noncomputable def physCoefCut (δ N Γ : ℝ) (f K J : ℕ) (P : Fin J → Fin S.H)
    (χ : Fin S.Kc → Fin 3) (l r : ℕ) : ℝ :=
  if l * r < K then physCoefAtom S δ N Γ f J P χ l r else 0

/-- **The actual Ordering-B cell** of the atom `(J, P, χ)` at scales `(L, R, N_n, M)`. -/
noncomputable def physCell (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K L R Nn M J : ℕ)
    (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3) (α β : ArithmeticFunction ℝ) : OBData where
  f := f
  c := c
  A := A
  B := B
  L := L
  R := R
  N := Nn
  M := M
  coef := physCoefCut S δ N Γ f K J P χ
  alpha := α
  beta := β

/-- The `h_l U_r` part of the exact Type-II split. -/
noncomputable def physUrem (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) (K K' : ℕ)
    (α β : ArithmeticFunction ℝ) : ℝ :=
  ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
    ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, physCoefCut S δ N Γ f K J P χ l r *
      ∑ v ∈ range K', (α * β) v * (resMask f c v * (hz A B l v * Uz r v))

variable {S}

/-- Dyadic decomposition of `[1, 2^n)`. -/
lemma sum_Ico_one_two_pow (n : ℕ) (g : ℕ → ℝ) :
    ∑ l ∈ Ico 1 (2 ^ n), g l = ∑ i ∈ range n, ∑ l ∈ Ico (2 ^ i) (2 * 2 ^ i), g l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, pow_succ, mul_comm (2 ^ n) 2]
    exact (sum_Ico_consecutive g (Nat.one_le_two_pow) (by omega)).symm

/-- Double dyadic decomposition of a coefficient vanishing for `l r ≥ K`. -/
lemma sum_box_dyadic {K n : ℕ} (hKn : K ≤ 2 ^ n) (G : ℕ → ℕ → ℝ)
    (hG : ∀ l r, K ≤ l * r → G l r = 0) :
    ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, G l r =
      ∑ i ∈ range n, ∑ i' ∈ range n, ∑ l ∈ Ico (2 ^ i) (2 * 2 ^ i),
        ∑ r ∈ Ico (2 ^ i') (2 * 2 ^ i'), G l r := by
  have h1 : ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, G l r =
      ∑ l ∈ Ico 1 (2 ^ n), ∑ r ∈ Ico 1 (2 ^ n), G l r := by
    have e : ∀ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, G l r = ∑ r ∈ Ico 1 (2 ^ n), G l r := by
      intro l hl
      apply sum_subset (Ico_subset_Ico_right hKn)
      intro r hr hr'
      simp only [mem_Ico, not_and, not_lt] at hr hr'
      rw [mem_Ico] at hl
      exact hG l r (le_trans (hr' hr.1) (Nat.le_mul_of_pos_left r (by omega)))
    rw [sum_congr rfl e]
    apply sum_subset (Ico_subset_Ico_right hKn)
    intro l hl hl'
    simp only [mem_Ico, not_and, not_lt] at hl hl'
    refine sum_eq_zero (fun r hr => hG l r ?_)
    rw [mem_Ico] at hr
    exact le_trans (hl' hl.1) (Nat.le_mul_of_pos_right l (by omega))
  rw [h1, sum_Ico_one_two_pow]
  refine sum_congr rfl (fun i _ => ?_)
  rw [← sum_comm, sum_Ico_one_two_pow]
  refine sum_congr rfl (fun i' _ => ?_)
  exact sum_comm

open Classical in
/-- **Exact composed Type-II source identity for one packet.** -/
theorem scalarTypeII_eq_cells (hS : S.Good) (δ N Γ : ℝ) (f c A : ℕ) (B : ℤ) {K n : ℕ}
    (hKn : K ≤ 2 ^ n) {Nn M K' : ℕ} (α β : ArithmeticFunction ℝ)
    (hα : ∀ m, α m ≠ 0 → Nn ≤ m ∧ m < 2 * Nn) (hβ : ∀ m, β m ≠ 0 → M ≤ m ∧ m < 2 * M)
    (hK' : 4 * Nn * M ≤ K') :
    scalarTypeII S Γ f c A B K K' α β =
      ∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
        ∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β).T +
      physUrem S δ N Γ f c A B K K' α β := by
  set w : ℕ → ℝ := fun v => (α * β) v * resMask f c v with hw
  -- Step A: move the `v`-sum outside
  have hA : scalarTypeII S Γ f c A B K K' α β = ∑ v ∈ range K', w v *
      (Γ * ∑ d ∈ Ico 1 K, if Nat.Coprime f d then S.ellX d * (Iz A B d v - Uz d v) else 0) := by
    unfold scalarTypeII
    rw [mul_sum]
    have : ∀ d ∈ Ico 1 K, Γ * (if Nat.Coprime f d then S.ellX d *
        ∑ v ∈ range K', (α * β) v * (resMask f c v * (Iz A B d v - Uz d v)) else 0) =
        ∑ v ∈ range K', w v * (Γ * (if Nat.Coprime f d then
          S.ellX d * (Iz A B d v - Uz d v) else 0)) := by
      intro d _
      split_ifs
      · rw [mul_sum, mul_sum]
        refine sum_congr rfl (fun v _ => ?_)
        simp only [hw]; ring
      · simp
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl (fun v _ => ?_)
    rw [mul_sum, mul_sum]
  -- Step B: the exact Type-II split atom by atom, for each `v`
  rw [hA]
  simp_rw [typeII_source_decomp hS δ N Γ f K A B]
  -- Step C: the right-hand side, expanded
  have hT : ∀ J (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3),
      ∑ i ∈ range n, ∑ i' ∈ range n,
          (physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β).T =
        ∑ l ∈ Ico 1 K, ∑ r ∈ Ico 1 K, physCoefCut S δ N Γ f K J P χ l r *
          ∑ v ∈ range K', (α * β) v * (resMask f c v * Iz A B l v * hz A B r v) := by
    intro J P χ
    rw [sum_box_dyadic hKn]
    · refine sum_congr rfl (fun i _ => sum_congr rfl (fun i' _ => ?_))
      rw [← OBData.source_eq_T (D := physCell S δ N Γ f c A B K (2 ^ i) (2 ^ i') Nn M J P χ α β)
        α β (fun _ => rfl) (fun _ => rfl) hα hβ hK']
      rfl
    · intro l r hlr
      simp [physCoefCut, not_lt.2 hlr]
  simp_rw [hT]
  unfold physUrem
  rw [← sum_add_distrib]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun J _ => ?_)
  rw [← sum_add_distrib, sum_comm]
  refine sum_congr rfl (fun P _ => ?_)
  rw [← sum_add_distrib, sum_comm]
  refine sum_congr rfl (fun χ _ => ?_)
  rw [← sum_add_distrib, sum_comm]
  refine sum_congr rfl (fun l _ => ?_)
  rw [← sum_add_distrib, sum_comm]
  refine sum_congr rfl (fun r _ => ?_)
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun v _ => ?_)
  simp only [physCoefCut, hw]
  split_ifs <;> ring

/-- **Packet-level composed identity**: the scalar Type-II sources of all labelled packets
`ξ ∈ Ξ`, each with its actual `Γ_ξ`, `f_ξ`, `c_ξ`, `A_ξ`, `B_ξ`, summed **once** over `Ξ`, equal
the sum of the actual Ordering-B cells plus the `h_l U_r` parts.  The designated pair
`(j(ξ), ℓ(ξ))` is part of the packet index; no further sum over designated coordinates occurs. -/
theorem packet_typeII_eq_cells (Pd : PhysData) (hS : S.Good) (δ : ℝ)
    (N : Packet Pd.k → ℝ) {K n : ℕ} (hKn : K ≤ 2 ^ n) (Nn M K' : Packet Pd.k → ℕ)
    (α β : Packet Pd.k → ArithmeticFunction ℝ)
    (hα : ∀ ξ m, α ξ m ≠ 0 → Nn ξ ≤ m ∧ m < 2 * Nn ξ)
    (hβ : ∀ ξ m, β ξ m ≠ 0 → M ξ ≤ m ∧ m < 2 * M ξ) (hK' : ∀ ξ, 4 * Nn ξ * M ξ ≤ K' ξ) :
    ∑ ξ ∈ Pd.XiAll, scalarTypeII S (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (K' ξ)
        (α ξ) (β ξ) =
      ∑ ξ ∈ Pd.XiAll,
        ((∑ J ∈ range (S.T ^ 2 + 1), ∑ P : Fin J → Fin S.H, ∑ χ : Fin S.Kc → Fin 3,
          ∑ i ∈ range n, ∑ i' ∈ range n,
            (physCell S δ (N ξ) (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (2 ^ i)
              (2 ^ i') (Nn ξ) (M ξ) J P χ (α ξ) (β ξ)).T) +
          physUrem S δ (N ξ) (Pd.Gamma ξ) (Pd.f ξ) (Pd.cRes ξ) (Pd.A ξ) (Pd.B ξ) K (K' ξ)
            (α ξ) (β ξ)) :=
  sum_congr rfl (fun ξ _ => scalarTypeII_eq_cells hS δ (N ξ) _ _ _ _ _ hKn (α ξ) (β ξ)
    (hα ξ) (hβ ξ) (hK' ξ))

/-- **Contract of every actual critical Type-II cell** (`δ = κ`, `N = N_n`). -/
theorem physCell_contract {κ : ℝ} (h : CritRegime S κ) {Nn : ℕ} (hN : CritCell S κ Nn)
    (Γ : ℝ) (f c A : ℕ) (B : ℤ) (K L R M J : ℕ) (P : Fin J → Fin S.H) (χ : Fin S.Kc → Fin 3)
    (α β : ArithmeticFunction ℝ) :
    let D := physCell S κ Nn Γ f c A B K L R Nn M J P χ α β
    let col := S.atomColour κ Nn J P
    let Q := (Nn : ℝ) * S.X ^ (-κ)
    let Sb := cprod (S.boxVec J P) col 1 J
    let Rb := cprod (S.boxVec J P) col 2 J
    (∀ l r, |D.coef l r| ≤ |Γ| * S.atomWeight J P col) ∧
      (∀ l r, D.coef l r ≠ 0 → S.BoxAdm J P ∧ Nat.Coprime l r ∧ Nat.Coprime f (l * r) ∧
        l * r < K ∧ (l : ℝ) ≤ Q ∧ ∃ a₂ a₃ : ℕ, a₂ * a₃ = r ∧ (a₂ : ℝ) ≤ Sb ∧ (a₃ : ℝ) ≤ Rb) ∧
      (S.BoxAdm J P →
        (Nn : ℝ) ^ 2 * Rb ^ 2 * Sb ≤ S.X ^ (1 - 8 * (κ / 2000)) ∧
        (Nn : ℝ) ^ ((71 : ℝ) / 50) * Rb * Sb ^ ((93 : ℝ) / 50) ≤ S.X ^ (1 - 16 * (κ / 2000)) ∧
        (Nn : ℝ) ^ ((39 : ℝ) / 25) * Q ^ ((11 : ℝ) / 25) * Rb ^ 2 * Sb ^ 5 ≤
          S.X ^ (2 - 32 * (κ / 2000))) := by
  intro D col Q Sb Rb
  have hS := h.good
  have hA := atomParams_of_crit h hN
  refine ⟨fun l r => ?_, fun l r hne => ?_, fun hP => ?_⟩
  · show |physCoefCut S κ Nn Γ f K J P χ l r| ≤ _
    unfold physCoefCut
    split_ifs
    · exact physCoefAtom_abs_le hS κ Nn Γ f J P χ l r
    · simp only [abs_zero]; exact mul_nonneg (abs_nonneg _) (atomWeight_nonneg P _)
  · change physCoefCut S κ Nn Γ f K J P χ l r ≠ 0 at hne
    unfold physCoefCut at hne
    split_ifs at hne with hlr
    · obtain ⟨h1, h2, h3⟩ := physCoefAtom_coprime hS hne
      obtain ⟨r1, r2, -, -⟩ := physCoefAtom_ranges hS hA hne
      exact ⟨h3, h1, h2, hlr, r1, r2⟩
    · exact absurd rfl hne
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, b1, b2, b3⟩ :=
      physAtom_provider_contract h hN Γ hP χ
    exact ⟨b1, b2, b3⟩

end Erdos287.Physical.TypeII
