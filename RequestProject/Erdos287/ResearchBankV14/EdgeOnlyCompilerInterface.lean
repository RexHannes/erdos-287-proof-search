import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import RequestProject.Erdos287.ResearchBankV9.GcdClique

/-!
# Erdős #287 — Research Bank V14 §A4: the edge-only CRT compiler (general theorem)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Provenance (honest record)

Before V14 the repository contained the *general (non-coprime) CRT*
`ResearchBankV9.GcdClique.crt_exists` / `crt_exists_ge` and the translation criterion
`gcd_eq_diff_iff`, but **no** theorem placing the offsets inside prescribed boxes: V9 records
`PrescribedShapeGCDClique` as not inhabited.  So there was no pre-existing *edge-only compiler with
boxes* to reuse.  V14 proves it here as a general theorem (not a toy statement), **reusing** the
V9 general CRT for the translation step.

## Statement (`prescribedShape_gcdClique`)

For an arbitrary finite vertex type `V`, arbitrary nonempty rational boxes `(lo v, hi v)` and every
scale threshold `T₀`, there are a scale `T ≥ T₀` and pairwise distinct integer offsets `b v` with
`lo v · T < b v < hi v · T` such that for **every** `N` there is a common translation `A ≥ N` with

    gcd(A + b u, A + b v) = |b u − b v|      for all u ≠ v.

Edge-only corollaries: `edgeOnly_compiler` (any finite simple graph) and
`edgeOnly_compiler_coloured` (the V14 contract verbatim: properly-coloured graph, pairwise
disjoint boxes).  The colouring and box-disjointness hypotheses turn out to be **unnecessary**
for existence.

## Construction

* `cliqueVals n` — an explicit `n`-element gcd-clique `β` (`(β_j − β_i) ∣ β_i`), recursively
  `{P} ∪ {P + s}` with `P` the product of the previous values;
* `α v = N x v + G^{idx v}` — box positions `x v` plus a `G`-adic perturbation making every
  resultant `R = (α_v−α_u)(β_z−β_y) − (α_z−α_y)(β_v−β_u)` of two disjoint pairs nonzero;
* `b v = α v t + β v` with `t` a multiple of every nonzero resultant;
* compatibility of `A ≡ −b u (mod |b v − b u|)` is proved prime-free: a common divisor `g` of two
  disjoint differences divides `R`, hence `t`, hence both `β`-differences, hence `β u` and `β y`
  (clique property), hence `b u − b y`;
* the V9 general CRT supplies an arbitrarily large translation `A`.

**Effectivity firewall.**  This is an existence theorem.  The construction is explicit and
computable in principle, but no quantitatively useful *height* bound (size of `T`, `A`) is
claimed; that remains OPEN.
-/

namespace Erdos287
namespace ResearchBankV14
namespace EdgeOnlyCompilerInterface

open ResearchBankV9.GcdClique

/-! ## 1. An explicit gcd-clique of every size -/

/-- `cliqueVals n i` (`i < n`): the values `{P} ∪ {P + s : s ∈ previous}`. -/
def cliqueVals : ℕ → ℕ → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun i =>
      match i with
      | 0 => ∏ j ∈ Finset.range n, cliqueVals n j
      | i + 1 => (∏ j ∈ Finset.range n, cliqueVals n j) + cliqueVals n i

theorem cliqueVals_pos : ∀ n i, 0 < cliqueVals n i
  | 0, _ => by simp [cliqueVals]
  | n + 1, 0 => by
      simp only [cliqueVals]
      exact Finset.prod_pos fun j _ => cliqueVals_pos n j
  | n + 1, i + 1 => by
      simp only [cliqueVals]
      have := Finset.prod_pos (s := Finset.range n) fun j _ => cliqueVals_pos n j
      have := cliqueVals_pos n i
      linarith

theorem cliqueVals_dvd_prod {n i : ℕ} (hi : i < n) :
    cliqueVals n i ∣ ∏ j ∈ Finset.range n, cliqueVals n j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi)

/-- **Clique property**: for `i ≠ j < n`, `β_i ≠ β_j` and `(β_j − β_i) ∣ β_i`. -/
theorem cliqueVals_clique : ∀ n i j, i < n → j < n → i ≠ j →
    cliqueVals n i ≠ cliqueVals n j ∧ (cliqueVals n j - cliqueVals n i) ∣ cliqueVals n i
  | 0, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, 0, 0, _, _, hij => absurd rfl hij
  | n + 1, 0, j + 1, _, hj, _ => by
      simp only [cliqueVals]
      have hp := cliqueVals_pos n j
      refine ⟨by intro h; linarith, ?_⟩
      rw [add_sub_cancel_left]
      exact cliqueVals_dvd_prod (by omega)
  | n + 1, i + 1, 0, hi, _, _ => by
      simp only [cliqueVals]
      have hp := cliqueVals_pos n i
      refine ⟨by intro h; linarith, ?_⟩
      rw [show (∏ j ∈ Finset.range n, cliqueVals n j) -
          ((∏ j ∈ Finset.range n, cliqueVals n j) + cliqueVals n i) = -cliqueVals n i by ring,
        neg_dvd]
      exact dvd_add (cliqueVals_dvd_prod (by omega)) dvd_rfl
  | n + 1, i + 1, j + 1, hi, hj, hij => by
      simp only [cliqueVals]
      obtain ⟨hne, hd⟩ := cliqueVals_clique n i j (by omega) (by omega) (by omega)
      refine ⟨by intro h; exact hne (by linarith), ?_⟩
      rw [show (∏ j ∈ Finset.range n, cliqueVals n j) + cliqueVals n j -
          ((∏ j ∈ Finset.range n, cliqueVals n j) + cliqueVals n i) =
          cliqueVals n j - cliqueVals n i by ring]
      exact dvd_add (hd.trans (cliqueVals_dvd_prod (by omega))) hd

theorem cliqueVals_4 : (List.range 4).map (cliqueVals 4) = [24, 26, 27, 28] := by decide

/-! ## 2. The `G`-adic domination lemma -/

theorem dom_ne_zero {G S : ℤ} (hG : 3 * S < G) (hS : 0 ≤ S) {a b c d : ℕ}
    (hb : b < a) (hc : c < a) (hd : d < a) {p q r s : ℤ} (hp : p ≠ 0)
    (hq : |q| ≤ S) (hr : |r| ≤ S) (hs : |s| ≤ S) :
    p * G ^ a + q * G ^ b + r * G ^ c + s * G ^ d ≠ 0 := by
  have hG1 : 1 ≤ G := by linarith
  have hGpos : 0 < G := by linarith
  have hpow : ∀ e, e < a → G ^ e ≤ G ^ (a - 1) := fun e he =>
    pow_le_pow_right₀ hG1 (by omega)
  have hbound : ∀ (x : ℤ) (e : ℕ), |x| ≤ S → e < a → |x * G ^ e| ≤ S * G ^ (a - 1) := by
    intro x e hx he
    rw [abs_mul, abs_of_pos (pow_pos hGpos e)]
    exact mul_le_mul hx (hpow e he) (pow_pos hGpos e).le hS
  have h1 := hbound q b hq hb
  have h2 := hbound r c hr hc
  have h3 := hbound s d hs hd
  have hA : G ^ a = G * G ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpa : G ^ a ≤ |p * G ^ a| := by
    rw [abs_mul, abs_of_pos (pow_pos hGpos a)]
    have : 1 ≤ |p| := Int.one_le_abs hp
    nlinarith [pow_pos hGpos a]
  intro h
  have hsum : |q * G ^ b + r * G ^ c + s * G ^ d| ≤ 3 * S * G ^ (a - 1) := by
    calc _ ≤ |q * G ^ b + r * G ^ c| + |s * G ^ d| := abs_add_le _ _
      _ ≤ |q * G ^ b| + |r * G ^ c| + |s * G ^ d| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have heq : p * G ^ a = -(q * G ^ b + r * G ^ c + s * G ^ d) := by linarith
  rw [heq, abs_neg] at hpa
  have hlt : 3 * S * G ^ (a - 1) < G ^ a := by
    rw [hA]; exact mul_lt_mul_of_pos_right hG (pow_pos hGpos _)
  linarith

/-- Four distinct `G`-adic monomials with nonzero coefficients `≤ S < G/3` cannot cancel. -/
theorem four_term_ne_zero {G S : ℤ} (hG : 3 * S < G) (hS : 0 ≤ S) {a b c d : ℕ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {p q r s : ℤ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hp' : |p| ≤ S) (hq' : |q| ≤ S) (hr' : |r| ≤ S) (hs' : |s| ≤ S) :
    p * G ^ a + q * G ^ b + r * G ^ c + s * G ^ d ≠ 0 := by
  have hcases : (b < a ∧ c < a ∧ d < a) ∨ (a < b ∧ c < b ∧ d < b) ∨
      (a < c ∧ b < c ∧ d < c) ∨ (a < d ∧ b < d ∧ c < d) := by omega
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact dom_ne_zero hG hS h1 h2 h3 hp hq' hr' hs'
  · have := dom_ne_zero hG hS h1 h2 h3 hq hp' hr' hs'
    intro h; apply this; linarith
  · have := dom_ne_zero hG hS h1 h2 h3 hr hp' hq' hs'
    intro h; apply this; linarith
  · have := dom_ne_zero hG hS h1 h2 h3 hs hp' hq' hr'
    intro h; apply this; linarith

/-- If `N * X + E = 0` with `|E| < N` then `E = 0`. -/
theorem eq_zero_of_mul_add {N X E : ℤ} (hE : |E| < N) (h : N * X + E = 0) : E = 0 := by
  have hdvd : N ∣ E := ⟨-X, by linarith⟩
  exact Int.eq_zero_of_abs_lt_dvd hdvd hE

/-! ## 3. Resultants and compatibility -/

section Construction

variable {V : Type*}

/-- Quadruple resultant `R = (α_v−α_u)(β_z−β_y) − (α_z−α_y)(β_v−β_u)`. -/
def resultant (α β : V → ℤ) (q : V × V × V × V) : ℤ :=
  (α q.2.1 - α q.1) * (β q.2.2.2 - β q.2.2.1) - (α q.2.2.2 - α q.2.2.1) * (β q.2.1 - β q.1)

/-- Product of all nonzero resultants (as a natural number). -/
def resultantProd [Fintype V] (α β : V → ℤ) : ℕ :=
  ∏ q : V × V × V × V, if resultant α β q = 0 then 1 else (resultant α β q).natAbs

theorem resultantProd_pos [Fintype V] (α β : V → ℤ) : 0 < resultantProd α β := by
  unfold resultantProd
  refine Finset.prod_pos fun q _ => ?_
  split_ifs with h
  · exact Nat.one_pos
  · exact Int.natAbs_pos.2 h

theorem resultant_dvd_prod [Fintype V] (α β : V → ℤ) (q : V × V × V × V) (h : resultant α β q ≠ 0) :
    resultant α β q ∣ (resultantProd α β : ℤ) := by
  have : (resultant α β q).natAbs ∣ resultantProd α β := by
    have := Finset.dvd_prod_of_mem
      (fun q => if resultant α β q = 0 then 1 else (resultant α β q).natAbs)
      (Finset.mem_univ q)
    simpa [h] using this
  exact Int.natAbs_dvd_natAbs.1 (by simpa using this)

/-- **Compatibility core** for two disjoint pairs. -/
theorem compat_core (α β : V → ℤ) (t : ℤ) (hβ : ∀ u v, u ≠ v → (β v - β u) ∣ β u)
    {u v y z : V} (hRt : resultant α β (u, v, y, z) ∣ t) (huv : u ≠ v) (hyz : y ≠ z) {g : ℤ}
    (h1 : g ∣ (α v * t + β v) - (α u * t + β u)) (h2 : g ∣ (α z * t + β z) - (α y * t + β y)) :
    g ∣ (α u * t + β u) - (α y * t + β y) := by
  have hgR : g ∣ resultant α β (u, v, y, z) := by
    have := dvd_sub (dvd_mul_of_dvd_right h1 (α z - α y)) (dvd_mul_of_dvd_right h2 (α v - α u))
    have e : (α z - α y) * ((α v * t + β v) - (α u * t + β u)) -
        (α v - α u) * ((α z * t + β z) - (α y * t + β y)) = -resultant α β (u, v, y, z) := by
      simp only [resultant]; ring
    rw [e, dvd_neg] at this; exact this
  have hgt : g ∣ t := hgR.trans hRt
  have hB : g ∣ β v - β u := by
    have := dvd_sub h1 (dvd_mul_of_dvd_right hgt (α v - α u))
    rwa [show (α v * t + β v) - (α u * t + β u) - (α v - α u) * t = β v - β u by ring] at this
  have hB' : g ∣ β z - β y := by
    have := dvd_sub h2 (dvd_mul_of_dvd_right hgt (α z - α y))
    rwa [show (α z * t + β z) - (α y * t + β y) - (α z - α y) * t = β z - β y by ring] at this
  have hu : g ∣ β u := hB.trans (hβ u v huv)
  have hy : g ∣ β y := hB'.trans (hβ y z hyz)
  have := dvd_add (dvd_mul_of_dvd_right hgt (α u - α y)) (dvd_sub hu hy)
  rwa [show (α u - α y) * t + (β u - β y) = (α u * t + β u) - (α y * t + β y) by ring] at this

/-- Compatibility of the full congruence system `A ≡ −b u (mod |b v − b u|)`. -/
theorem compat_all [DecidableEq V] (α β : V → ℤ) (t : ℤ) (hβ : ∀ u v, u ≠ v → (β v - β u) ∣ β u)
    (hR : ∀ u v y z, u ≠ v → u ≠ y → u ≠ z → v ≠ y → v ≠ z → y ≠ z →
      resultant α β (u, v, y, z) ∣ t)
    {u v y z : V} (huv : u ≠ v) (hyz : y ≠ z) {g : ℤ}
    (h1 : g ∣ (α v * t + β v) - (α u * t + β u)) (h2 : g ∣ (α z * t + β z) - (α y * t + β y)) :
    g ∣ (α u * t + β u) - (α y * t + β y) := by
  by_cases e1 : u = y
  · subst e1; simp
  by_cases e2 : u = z
  · subst e2; exact h2
  by_cases e3 : v = y
  · subst e3
    have := dvd_neg.2 h1; rwa [neg_sub] at this
  by_cases e4 : v = z
  · subst e4
    have := dvd_sub h2 h1
    rwa [show α v * t + β v - (α y * t + β y) - (α v * t + β v - (α u * t + β u)) =
      α u * t + β u - (α y * t + β y) by ring] at this
  exact compat_core α β t hβ (hR u v y z huv e1 e2 e3 e4 hyz) huv hyz h1 h2

end Construction

/-! ## 4. The general theorem -/

/-- **Prescribed-shape gcd-clique theorem (general, all pairs).** -/
theorem prescribedShape_gcdClique {V : Type*} [Fintype V] [DecidableEq V]
    (lo hi : V → ℚ) (hbox : ∀ v, lo v < hi v) (T₀ : ℕ) :
    ∃ (T : ℕ) (b : V → ℤ), 0 < T ∧ T₀ ≤ T ∧
      (∀ v, lo v * T < b v ∧ (b v : ℚ) < hi v * T) ∧ (∀ u v, u ≠ v → b u ≠ b v) ∧
      ∀ N : ℤ, ∃ A : ℤ, N ≤ A ∧
        ∀ u v, u ≠ v → Int.gcd (A + b u) (A + b v) = (b u - b v).natAbs := by
  classical
  set n := Fintype.card V
  set e := Fintype.equivFin V
  set idx : V → ℕ := fun v => (e v : ℕ) with hidx
  have hidx_inj : Function.Injective idx := fun u v h => e.injective (Fin.ext h)
  have hidx_lt : ∀ v, idx v < n := fun v => (e v).isLt
  -- the clique values
  set β : V → ℤ := fun v => cliqueVals n (idx v) with hβdef
  have hβpos : ∀ v, 0 < β v := fun v => cliqueVals_pos _ _
  have hβcl : ∀ u v, u ≠ v → β u ≠ β v ∧ (β v - β u) ∣ β u := fun u v huv =>
    cliqueVals_clique n (idx u) (idx v) (hidx_lt u) (hidx_lt v)
      (fun h => huv (hidx_inj h))
  set S : ℤ := ∑ v, β v with hS
  have hβle : ∀ v, β v ≤ S := fun v =>
    Finset.single_le_sum (fun w _ => (hβpos w).le) (Finset.mem_univ v)
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun w _ => (hβpos w).le
  have hdiff : ∀ u v, |β v - β u| ≤ S := fun u v => by
    rw [abs_le]; constructor <;> linarith [hβpos u, hβpos v, hβle u, hβle v]
  -- `G`, `N`
  set G : ℤ := 3 * S + 1 with hG
  have hG3 : 3 * S < G := by omega
  have hG2 : 1 ≤ G := by omega
  have hGpos : 0 < G := by omega
  set N : ℤ := 4 * (S + 1) * G ^ n + 1 with hN
  have hGn : ∀ v, 0 < G ^ idx v ∧ G ^ idx v ≤ G ^ n := fun v =>
    ⟨pow_pos hGpos _, pow_le_pow_right₀ hG2 (hidx_lt v).le⟩
  have hGnpos : 0 < G ^ n := pow_pos hGpos n
  have hNpos : 0 < N := by positivity
  have hGltN : ∀ v, G ^ idx v < N := fun v => by
    have := (hGn v).2; nlinarith
  have hSltN : S < N := by nlinarith
  -- the scale `D` and box positions `x`
  set D : ℕ := ∑ v, ⌈3 / (hi v - lo v)⌉₊ + 1 with hD
  have hDgap : ∀ v, 3 < (D : ℚ) * (hi v - lo v) := by
    intro v
    have hgap : 0 < hi v - lo v := sub_pos.2 (hbox v)
    have h1 : ⌈3 / (hi v - lo v)⌉₊ ≤ ∑ w, ⌈3 / (hi w - lo w)⌉₊ :=
      Finset.single_le_sum (f := fun w => ⌈3 / (hi w - lo w)⌉₊) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ v)
    have h2 : 3 / (hi v - lo v) ≤ ⌈3 / (hi v - lo v)⌉₊ := Nat.le_ceil _
    have h3 : (3 / (hi v - lo v) : ℚ) < D := by
      have : ((⌈3 / (hi v - lo v)⌉₊ : ℕ) : ℚ) ≤ (∑ w, ⌈3 / (hi w - lo w)⌉₊ : ℕ) := by
        exact_mod_cast h1
      rw [hD]; push_cast at this ⊢; linarith
    rwa [div_lt_iff₀ hgap] at h3
  have hDpos : (0 : ℚ) < D := by rw [hD]; positivity
  set x : V → ℤ := fun v => ⌊lo v * D⌋ + 1 with hx
  have hx1 : ∀ v, lo v * D < x v := fun v => by
    simp only [hx]; push_cast; exact Int.lt_floor_add_one _
  have hx2 : ∀ v, (x v : ℚ) ≤ lo v * D + 1 := fun v => by
    simp only [hx]; push_cast; linarith [Int.floor_le (lo v * D)]
  -- `α`
  set α : V → ℤ := fun v => N * x v + G ^ idx v with hα
  -- resultants of disjoint quadruples are nonzero
  have hRne : ∀ u v y z, u ≠ v → u ≠ y → u ≠ z → v ≠ y → v ≠ z → y ≠ z →
      resultant α β (u, v, y, z) ≠ 0 := by
    intro u v y z huv huy huz hvy hvz hyz hR0
    set B := β v - β u with hBdef
    set B' := β z - β y with hB'def
    have hB : B ≠ 0 := sub_ne_zero.2 (hβcl u v huv).1.symm
    have hB' : B' ≠ 0 := sub_ne_zero.2 (hβcl y z hyz).1.symm
    have hsplit : resultant α β (u, v, y, z) =
        N * ((x v - x u) * B' - (x z - x y) * B) +
          (B' * G ^ idx v + (-B') * G ^ idx u + (-B) * G ^ idx z + B * G ^ idx y) := by
      simp only [resultant, hα, hBdef, hB'def]; ring
    have hb1 : |B| ≤ S := hdiff u v
    have hb2 : |B'| ≤ S := hdiff y z
    have hEbound :
        |B' * G ^ idx v + (-B') * G ^ idx u + (-B) * G ^ idx z + B * G ^ idx y| < N := by
      have ht : ∀ (c : ℤ) (w : V), |c| ≤ S → |c * G ^ idx w| ≤ S * G ^ n := fun c w hc => by
        rw [abs_mul, abs_of_pos (hGn w).1]
        exact mul_le_mul hc (hGn w).2 (hGn w).1.le hSnn
      have e1 := ht B' v hb2
      have e2 := ht (-B') u (by rwa [abs_neg])
      have e3 := ht (-B) z (by rwa [abs_neg])
      have e4 := ht B y hb1
      calc _ ≤ |B' * G ^ idx v + (-B') * G ^ idx u + (-B) * G ^ idx z| + |B * G ^ idx y| :=
            abs_add_le _ _
        _ ≤ |B' * G ^ idx v + (-B') * G ^ idx u| + |(-B) * G ^ idx z| + |B * G ^ idx y| := by
            gcongr; exact abs_add_le _ _
        _ ≤ |B' * G ^ idx v| + |(-B') * G ^ idx u| + |(-B) * G ^ idx z| + |B * G ^ idx y| := by
            gcongr; exact abs_add_le _ _
        _ ≤ 4 * S * G ^ n := by linarith
        _ < N := by rw [hN]; nlinarith
    rw [hsplit] at hR0
    have hE0 := eq_zero_of_mul_add hEbound hR0
    have hi1 : idx v ≠ idx u := fun h => huv (hidx_inj h).symm
    have hi2 : idx v ≠ idx z := fun h => hvz (hidx_inj h)
    have hi3 : idx v ≠ idx y := fun h => hvy (hidx_inj h)
    have hi4 : idx u ≠ idx z := fun h => huz (hidx_inj h)
    have hi5 : idx u ≠ idx y := fun h => huy (hidx_inj h)
    have hi6 : idx z ≠ idx y := fun h => hyz (hidx_inj h).symm
    exact four_term_ne_zero hG3 hSnn hi1 hi2 hi3 hi4 hi5 hi6 hB' (neg_ne_zero.2 hB')
      (neg_ne_zero.2 hB) hB hb2 (by rwa [abs_neg]) (by rwa [abs_neg]) hb1 hE0
  -- `t`
  set t : ℕ := (S.toNat + 1) * resultantProd α β * (T₀ + 1) with ht
  have hRP := resultantProd_pos α β
  have htpos : 0 < t := by positivity
  have hRt : ∀ u v y z, u ≠ v → u ≠ y → u ≠ z → v ≠ y → v ≠ z → y ≠ z →
      resultant α β (u, v, y, z) ∣ (t : ℤ) := by
    intro u v y z h1 h2 h3 h4 h5 h6
    have hne := hRne u v y z h1 h2 h3 h4 h5 h6
    refine (resultant_dvd_prod α β _ hne).trans ?_
    rw [ht]; push_cast
    exact ⟨(S.toNat + 1 : ℤ) * (T₀ + 1), by ring⟩
  -- offsets and scale
  set b : V → ℤ := fun v => α v * t + β v with hb
  set T : ℕ := N.toNat * D * t with hT
  have hNT : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hNpos.le
  have hTq : (T : ℚ) = (N : ℚ) * D * t := by
    rw [hT]; push_cast
    rw [show ((N.toNat : ℕ) : ℚ) = ((N.toNat : ℤ) : ℚ) by push_cast; rfl, hNT]
  -- α injective ⇒ offsets distinct
  have hαinj : ∀ u v, u ≠ v → α u ≠ α v := by
    intro u v huv h
    have hE : G ^ idx u - G ^ idx v = 0 := by
      apply eq_zero_of_mul_add (N := N) (X := x u - x v)
      · rw [abs_lt]; constructor <;> linarith [hGltN u, hGltN v, (hGn u).1, (hGn v).1]
      · simp only [hα] at h; linear_combination h
    have hGG : G ^ idx u = G ^ idx v := by linarith
    have hS1 : 1 ≤ S := by have := hβle u; have := hβpos u; omega
    have hg : 1 < G := by omega
    exact huv (hidx_inj ((pow_right_strictMono₀ hg).injective hGG))
  have hbne : ∀ u v, u ≠ v → b u ≠ b v := by
    intro u v huv h
    have hα' := hαinj u v huv
    have h1 : (α u - α v) * t = β v - β u := by simp only [hb] at h; linarith
    have h2 : 1 ≤ |α u - α v| := Int.one_le_abs (sub_ne_zero.2 hα')
    have htS : S < (t : ℤ) := by
      have e1 : (S.toNat + 1 : ℕ) ≤ t := by
        rw [ht, mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
      have e2 : S ≤ (S.toNat : ℤ) := Int.self_le_toNat S
      have : ((S.toNat + 1 : ℕ) : ℤ) ≤ (t : ℤ) := by exact_mod_cast e1
      push_cast at this; linarith
    have h3 : (t : ℤ) ≤ |(α u - α v) * t| := by
      rw [abs_mul, abs_of_pos (by exact_mod_cast htpos : (0 : ℤ) < t)]
      exact le_mul_of_one_le_left (by positivity) h2
    rw [h1] at h3
    have := hdiff u v
    linarith
  refine ⟨T, b, ?_, ?_, ?_, hbne, ?_⟩
  · rw [hT]
    have : 0 < N.toNat := by omega
    have : 0 < D := by exact_mod_cast hDpos
    positivity
  · rw [hT]
    have h1 : 1 ≤ N.toNat := by omega
    have h2 : 1 ≤ D := by exact_mod_cast hDpos
    have h3 : T₀ + 1 ≤ t := by
      rw [ht]; exact Nat.le_mul_of_pos_left _ (by positivity)
    calc T₀ ≤ t := by omega
      _ = 1 * 1 * t := by ring
      _ ≤ N.toNat * D * t := by gcongr
  · intro v
    have htq : (0 : ℚ) < t := by exact_mod_cast htpos
    have hNq : (0 : ℚ) < N := by exact_mod_cast hNpos
    have hbq : (b v : ℚ) = N * x v * t + (G : ℚ) ^ idx v * t + β v := by
      simp only [hb, hα]; push_cast; ring
    have hGv : (0 : ℚ) < (G : ℚ) ^ idx v := by exact_mod_cast (hGn v).1
    have hGvN : (G : ℚ) ^ idx v < N := by exact_mod_cast hGltN v
    have hβv : (0 : ℚ) < β v := by exact_mod_cast hβpos v
    have hβvN : (β v : ℚ) < N * t := by
      have : β v < N * t := by
        calc β v ≤ S := hβle v
          _ < N := hSltN
          _ = N * 1 := by ring
          _ ≤ N * t := by
              have : (1 : ℤ) ≤ t := by exact_mod_cast htpos
              exact mul_le_mul_of_nonneg_left this hNpos.le
      exact_mod_cast this
    rw [hTq, hbq]
    constructor
    · have := hx1 v
      have hxx : lo v * D * (N * t) < x v * (N * t) :=
        mul_lt_mul_of_pos_right this (by positivity)
      linarith [mul_pos hGv htq]
    · have hx2v := hx2 v
      have hgap := hDgap v
      have e1 : (x v : ℚ) * (N * t) ≤ (lo v * D + 1) * (N * t) :=
        mul_le_mul_of_nonneg_right hx2v (by positivity)
      have e2 : (G : ℚ) ^ idx v * t < N * t := mul_lt_mul_of_pos_right hGvN htq
      have e3 : (lo v * D + 3) * (N * t) < hi v * D * (N * t) := by
        apply mul_lt_mul_of_pos_right _ (by positivity); linarith
      linarith
  · intro N₀
    set pairsV : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter fun p => p.1 ≠ p.2
      with hpairsV
    set l : List (ℤ × ℕ) := pairsV.toList.map fun p => (-b p.1, (b p.2 - b p.1).natAbs) with hl
    have hmem : ∀ q ∈ l, ∃ u v, u ≠ v ∧ q = (-b u, (b v - b u).natAbs) := by
      intro q hq
      simp only [hl, List.mem_map, Finset.mem_toList, hpairsV, Finset.mem_filter,
        Finset.mem_product, Finset.mem_univ, true_and] at hq
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := hq
      exact ⟨u, v, huv, rfl⟩
    have hne : ∀ q ∈ l, q.2 ≠ 0 := by
      intro q hq
      obtain ⟨u, v, huv, rfl⟩ := hmem q hq
      simp only [ne_eq, Int.natAbs_eq_zero, sub_eq_zero]
      exact (hbne u v huv).symm
    have hc : ∀ q ∈ l, ∀ r ∈ l, ((Nat.gcd q.2 r.2 : ℕ) : ℤ) ∣ q.1 - r.1 := by
      intro q hq r hr
      obtain ⟨u, v, huv, rfl⟩ := hmem q hq
      obtain ⟨y, z, hyz, rfl⟩ := hmem r hr
      have hdA : ∀ w : ℤ, ((w.natAbs : ℕ) : ℤ) ∣ w := fun w => by
        rw [Int.natCast_natAbs]; exact (abs_dvd _ _).2 dvd_rfl
      have h1 : ((Nat.gcd (b v - b u).natAbs (b z - b y).natAbs : ℕ) : ℤ) ∣ b v - b u :=
        (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (hdA _)
      have h2 : ((Nat.gcd (b v - b u).natAbs (b z - b y).natAbs : ℕ) : ℤ) ∣ b z - b y :=
        (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans (hdA _)
      have := compat_all α β t (fun u v huv => (hβcl u v huv).2) hRt huv hyz h1 h2
      simp only
      rw [show -b u - -b y = -(b u - b y) by ring, dvd_neg]
      exact this
    obtain ⟨A, hA0, hA⟩ := crt_exists_ge l hne hc N₀
    refine ⟨A, hA0, fun u v huv => ?_⟩
    have hq : (-b u, (b v - b u).natAbs) ∈ l := by
      simp only [hl, List.mem_map, Finset.mem_toList, hpairsV, Finset.mem_filter,
        Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨(u, v), huv, rfl⟩
    have hd := hA _ hq
    simp only [sub_neg_eq_add, Int.natCast_natAbs] at hd
    have hd' : (b v - b u) ∣ A + b u := (abs_dvd _ _).1 hd
    have := (gcd_eq_diff_iff (A + b u) (A + b v)).2
      (by rwa [show A + b v - (A + b u) = b v - b u by ring])
    rw [this, show A + b v - (A + b u) = b v - b u by ring, ← Int.natAbs_neg, neg_sub]

/-- **Edge-only compiler** for an arbitrary finite simple graph. -/
theorem edgeOnly_compiler {V : Type*} [Fintype V] [DecidableEq V] (Gr : SimpleGraph V)
    (lo hi : V → ℚ) (hbox : ∀ v, lo v < hi v) (T₀ : ℕ) :
    ∃ (T : ℕ) (b : V → ℤ), 0 < T ∧ T₀ ≤ T ∧
      (∀ v, lo v * T < b v ∧ (b v : ℚ) < hi v * T) ∧ (∀ u v, u ≠ v → b u ≠ b v) ∧
      ∀ N : ℤ, ∃ A : ℤ, N ≤ A ∧
        ∀ u v, Gr.Adj u v → Int.gcd (A + b u) (A + b v) = (b u - b v).natAbs := by
  obtain ⟨T, b, h1, h2, h3, h4, h5⟩ := prescribedShape_gcdClique lo hi hbox T₀
  refine ⟨T, b, h1, h2, h3, h4, fun N => ?_⟩
  obtain ⟨A, hA, hg⟩ := h5 N
  exact ⟨A, hA, fun u v huv => hg u v (Gr.ne_of_adj huv)⟩

end EdgeOnlyCompilerInterface
end ResearchBankV14
end Erdos287
