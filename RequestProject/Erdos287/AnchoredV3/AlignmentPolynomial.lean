import RequestProject.Erdos287.AnchoredV3.GlobalColumnCompiler
import RequestProject.Erdos287.AnchoredV3.MobilityStructure

/-!
# Anchored V3 — the exact combined alignment coefficient

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Fix a preparation `ω`, a terminal bank `B` on it, and reserved mobility positions
`Z = {n₀, …, n_{H-1}}` with `n i ∣ D`.  Write

```
S_y = S_* + ∑_{i ∈ y} 1 / n i,      T_y = D (1 - S_y) = T_* - ∑_{i ∈ y} D / n i.
```

Let `F` be the fixed terminal support object (the exact support of the terminal weight
polynomial, i.e. the set of `t` with `B.InSupport t`) and let

```
M_Z = { ∑_{i ∈ y} D / n i : y ⊆ Z }
```

be the support of `M_Z(X) = ∏_{n ∈ Z} (1 + X^{D/n})`.  The central V3 theorem
`alignment_coefficient` is the exact equivalence

```
(∃ mobility choice y and globally band-neutral terminal choice with S_y + Δ = 1)
  ↔  T_*  ∈  F + M_Z,
```

i.e. the coefficient of `X^{T_*}` in `F(X) M_Z(X)` is positive.  No probabilistic or asymptotic
input is used.

Finally `mobility_cofactor_gcd` records the exact mobility coset: under pairwise coprimality
with private factors, `gcd { D / n : n ∈ Z } = D / G` with `G = ∏ n`, so all mobility targets
stay in one explicit congruence coset.  This does **not** claim that mobility alone can solve a
pre-existing terminal lattice obstruction.
-/

open scoped BigOperators Pointwise

namespace Erdos287
namespace AnchoredV3

/-- A fixed terminal bank together with reserved mobility positions. -/
structure AlignedBank (H : ℕ) where
  /-- the preparation data -/
  ω : Prep
  /-- the fixed terminal bank -/
  B : Bank ω
  /-- the reserved mobility positions -/
  n : Fin H → ℕ
  /-- the reserved positions are positive -/
  hn_pos : ∀ i, 0 < n i
  /-- the reserved positions divide the global modulus -/
  hn_dvd : ∀ i, n i ∣ ω.D
  /-- the baseline preparation -/
  Sstar : ℚ
  /-- the baseline integer target -/
  Tstar : ℕ
  /-- the baseline target is exact -/
  hTstar : (ω.D : ℚ) * (1 - Sstar) = (Tstar : ℚ)
  /-- mobility never overshoots the baseline target -/
  hfit : ∀ y : Finset (Fin H), ∑ i ∈ y, ω.D / n i ≤ Tstar

namespace AlignedBank

variable {H : ℕ} (A : AlignedBank H)

/-- The moved baseline. -/
def S (y : Finset (Fin H)) : ℚ := A.Sstar + ∑ i ∈ y, (1 : ℚ) / ((A.n i : ℕ) : ℚ)

/-- The integer mobility weight of a mobility choice. -/
def mobWeight (y : Finset (Fin H)) : ℕ := ∑ i ∈ y, A.ω.D / A.n i

/-- The moved integer target. -/
def T (y : Finset (Fin H)) : ℕ := A.Tstar - A.mobWeight y

theorem mobWeight_add_T (y : Finset (Fin H)) : A.T y + A.mobWeight y = A.Tstar := by
  have := A.hfit y
  simp only [T, mobWeight]
  omega

/-- **The exact target movement in the aligned setting.** -/
theorem target_moved (y : Finset (Fin H)) :
    (A.ω.D : ℚ) * (1 - A.S y) = (A.T y : ℚ) := by
  have hterm : ∀ i ∈ y, (A.ω.D : ℚ) * ((1 : ℚ) / ((A.n i : ℕ) : ℚ))
      = ((A.ω.D / A.n i : ℕ) : ℚ) := by
    intro i _
    have hni : (0:ℚ) < ((A.n i : ℕ) : ℚ) := by exact_mod_cast A.hn_pos i
    have hcast : ((A.n i : ℕ) : ℚ) * ((A.ω.D / A.n i : ℕ) : ℚ) = (A.ω.D : ℚ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (Nat.mul_div_cancel' (A.hn_dvd i))
    rw [mul_one_div, div_eq_iff hni.ne']
    linarith [hcast, mul_comm ((A.n i : ℕ) : ℚ) ((A.ω.D / A.n i : ℕ) : ℚ)]
  have hexp : (A.ω.D : ℚ) * (1 - A.S y)
      = (A.ω.D : ℚ) * (1 - A.Sstar) - (A.ω.D : ℚ) * ∑ i ∈ y, (1 : ℚ) / ((A.n i : ℕ) : ℚ) := by
    rw [S]
    ring
  rw [hexp, Finset.mul_sum, Finset.sum_congr rfl hterm, A.hTstar]
  have hsum : ∑ i ∈ y, ((A.ω.D / A.n i : ℕ) : ℚ) = (A.mobWeight y : ℚ) := by
    rw [mobWeight, Nat.cast_sum]
  rw [hsum]
  have := A.mobWeight_add_T y
  have : (A.T y : ℚ) + (A.mobWeight y : ℚ) = (A.Tstar : ℚ) := by exact_mod_cast this
  linarith

/-- The support of the mobility factor `M_Z(X) = ∏_{n ∈ Z} (1 + X^{D/n})`. -/
def mobSupport : Finset ℕ := (Finset.univ : Finset (Finset (Fin H))).image A.mobWeight

theorem mem_mobSupport_iff {w : ℕ} : w ∈ A.mobSupport ↔ ∃ y : Finset (Fin H), A.mobWeight y = w := by
  classical
  simp [mobSupport]

/-- **The exact combined alignment coefficient identity.**

There is a mobility choice `y` and a globally band-neutral terminal choice with `S_y + Δ = 1`
if and only if `T_*` is the sum of a terminal support weight and a mobility weight — that is,
iff the coefficient of `X^{T_*}` in `F(X) M_Z(X)` is positive. -/
theorem alignment_coefficient :
    (∃ y : Finset (Fin H), ∃ sel : ℕ → Finset ℕ,
        A.B.Neutral sel ∧ A.S y + A.B.delta sel = 1) ↔
      ∃ y : Finset (Fin H), ∃ t : ℕ, A.B.InSupport t ∧ t + A.mobWeight y = A.Tstar := by
  constructor
  · rintro ⟨y, sel, hneutral, hexact⟩
    refine ⟨y, A.T y, ?_, A.mobWeight_add_T y⟩
    exact (A.B.globalColumnCompiler (A.S y) (A.T y) (A.target_moved y)).mp ⟨sel, hneutral, hexact⟩
  · rintro ⟨y, t, ht, hsum⟩
    have hTy : t = A.T y := by
      have := A.mobWeight_add_T y
      omega
    rw [hTy] at ht
    obtain ⟨sel, hneutral, hexact⟩ :=
      (A.B.globalColumnCompiler (A.S y) (A.T y) (A.target_moved y)).mpr ht
    exact ⟨y, sel, hneutral, hexact⟩

/-- **The sumset form of the alignment coefficient.**  If `Fsupp` is the exact terminal support
object, the exact fixed-bank completion exists iff `T_* ∈ Fsupp + M_Z`. -/
theorem alignment_sumset (Fsupp : Finset ℕ) (hF : ∀ t, t ∈ Fsupp ↔ A.B.InSupport t) :
    (∃ y : Finset (Fin H), ∃ sel : ℕ → Finset ℕ,
        A.B.Neutral sel ∧ A.S y + A.B.delta sel = 1) ↔
      A.Tstar ∈ Fsupp + A.mobSupport := by
  rw [A.alignment_coefficient]
  constructor
  · rintro ⟨y, t, ht, hsum⟩
    exact Finset.mem_add.mpr ⟨t, (hF t).mpr ht, A.mobWeight y,
      (A.mem_mobSupport_iff).mpr ⟨y, rfl⟩, hsum⟩
  · intro hmem
    obtain ⟨t, ht, w, hw, hsum⟩ := Finset.mem_add.mp hmem
    obtain ⟨y, rfl⟩ := (A.mem_mobSupport_iff).mp hw
    exact ⟨y, t, (hF t).mp ht, hsum⟩

end AlignedBank

/-- **The exact mobility congruence coset.**  For pairwise coprime mobility denominators with
private primes and `G = ∏ n i ∣ D`, the gcd of the mobility steps `D / n i` is `D / G`. -/
theorem mobility_cofactor_gcd {H : ℕ} (F : MobilityFamily H) (hH : 0 < H) {D : ℕ}
    (hGD : F.G ∣ D) :
    (Finset.univ.gcd (fun i => D / F.n i)) = D / F.G := by
  classical
  have hstep : ∀ i : Fin H, D / F.n i = (D / F.G) * F.a i := by
    intro i
    obtain ⟨c, hc⟩ := hGD
    have hG : F.n i * F.a i = F.G := F.n_mul_a i
    have hDG : D / F.G = c := by
      rw [hc]
      exact Nat.mul_div_cancel_left c (by
        rw [← hG]
        exact Nat.mul_pos (F.hpos i) (Finset.prod_pos (fun k _ => F.hpos k)))
    have hDn : D = F.n i * (F.a i * c) := by
      rw [hc, ← hG]; ring
    rw [hDG, hDn, Nat.mul_div_cancel_left _ (F.hpos i), mul_comm]
  rw [Finset.gcd_congr rfl (fun i _ => hstep i), Finset.gcd_mul_left,
    F.gcd_cofactors_eq_one hH]
  simp

end AnchoredV3
end Erdos287
