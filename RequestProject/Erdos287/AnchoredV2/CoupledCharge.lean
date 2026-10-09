import RequestProject.Erdos287.AnchoredV2.UnitSubsetSum

/-!
# Anchored V2 — the coupled `2^e × p` charge theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Each repair site carries two charges, a unit `a` modulo `2^e` and a unit `b` modulo an odd
prime `p`.  Since `2^e` and `p` are coprime, the Chinese remainder isomorphism

`ZMod (2^e * p) ≃+* ZMod (2^e) × ZMod p`

combines them into a single unit modulo `2^e p`.  Applying the unit-list subset-sum theorem in
`ZMod (2^e p)` gives the finite algebraic heart of a coupled batch: a long enough list of sites
contains a subset whose total charge is `0 (mod 2^e)` and any prescribed `t (mod p)`.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

/-- `2^e` and an odd prime `p` are coprime. -/
theorem coprime_two_pow_prime {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    Nat.Coprime (2 ^ e) p :=
  Nat.Coprime.pow_left e ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))

/-- The combined charge of a site: the CRT preimage of its `2^e`-charge and its `p`-charge. -/
noncomputable def coupledCharge {p e : ℕ} (h : Nat.Coprime (2 ^ e) p)
    (a : ZMod (2 ^ e)) (b : ZMod p) : ZMod (2 ^ e * p) :=
  (ZMod.chineseRemainder h).symm (a, b)

/-- The combined charge of two units is a unit. -/
theorem isUnit_coupledCharge {p e : ℕ} (h : Nat.Coprime (2 ^ e) p) {a : ZMod (2 ^ e)}
    {b : ZMod p} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (coupledCharge h a b) := by
  have hpair : IsUnit ((a, b) : ZMod (2 ^ e) × ZMod p) := Prod.isUnit_iff.2 ⟨ha, hb⟩
  exact hpair.map (ZMod.chineseRemainder h).symm

/-- **`coupled_subset_sum`.**  The coupled `2^e × p` charge theorem: given enough repair sites,
each with a unit charge modulo `2^e` and a unit charge modulo the odd prime `p`, some subset of
the sites has total charge exactly `0` modulo `2^e` and exactly the prescribed `t` modulo `p`. -/
theorem coupled_subset_sum {p e n : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hn : 2 ^ e * p - 1 ≤ n) (a : Fin n → ZMod (2 ^ e)) (b : Fin n → ZMod p)
    (ha : ∀ i, IsUnit (a i)) (hb : ∀ i, IsUnit (b i)) (t : ZMod p) :
    ∃ I : Finset (Fin n), (∑ i ∈ I, a i = 0) ∧ (∑ i ∈ I, b i = t) := by
  classical
  have hco : Nat.Coprime (2 ^ e) p := coprime_two_pow_prime hp hodd
  have hp2 : 2 ≤ p := hp.two_le
  have he2 : 2 ≤ 2 ^ e := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hm : 2 ≤ 2 ^ e * p := le_trans he2 (Nat.le_mul_of_pos_right _ (by omega))
  set c : Fin n → ZMod (2 ^ e * p) := fun i => coupledCharge hco (a i) (b i) with hc
  have hcu : ∀ i, IsUnit (c i) := fun i => isUnit_coupledCharge hco (ha i) (hb i)
  obtain ⟨I, hI⟩ := exists_subset_sum_eq hm hn c hcu
    ((ZMod.chineseRemainder hco).symm (0, t))
  have key : (ZMod.chineseRemainder hco) (∑ i ∈ I, c i) = (0, t) := by
    rw [hI]
    exact (ZMod.chineseRemainder hco).apply_symm_apply _
  have hci : ∀ i, (ZMod.chineseRemainder hco) (c i) = (a i, b i) := by
    intro i
    exact (ZMod.chineseRemainder hco).apply_symm_apply _
  rw [map_sum] at key
  have key' : ∑ i ∈ I, ((a i, b i) : ZMod (2 ^ e) × ZMod p) = (0, t) := by
    rw [← key]
    exact (Finset.sum_congr rfl fun i _ => (hci i).symm)
  refine ⟨I, ?_, ?_⟩
  · have := congrArg Prod.fst key'
    simpa [Prod.fst_sum] using this
  · have := congrArg Prod.snd key'
    simpa [Prod.snd_sum] using this

end AnchoredV2
end Erdos287
