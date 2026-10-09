# Erdős #287 — Anchored V4 continuation state

## 1. Frozen bank

* `RequestProject/Erdos287/AnchoredV2/**` — frozen.
* `RequestProject/Erdos287/AnchoredV3/**`, `AnchoredV3.lean` — frozen: global multiplier
  neutrality and the rowwise firewall, the old-empty/new-global-hit certificate, the fixed-bank
  global column compiler, column zero-sum packets with the packet-abundance firewall, the Boolean
  column gcd theorem with its sharpness witness, target mobility (`den(S_y) ∣ D_core`, exact target
  movement, mobility coset), the alignment coefficient and its sumset form, and the conditional
  Fourier/centrality/resonance interfaces.

## 2. New V4 bank (`RequestProject/Erdos287/AnchoredV4/**`)

Unconditional:

* `normalizedHeight_le_iff_dvd_two_lcm`, `prime_pow_dvd_L_iff`, `two_factor_essential`,
  `normalizedHeight_not_le_iff_dvd_lcm`, `normHeight_le_self`.
* `den_two_mul_dvd_iff`, `den_two_mul_dvd_L_iff_normHeight`, `den_recip_two_mul`,
  `doubled_lattice_regression`, `den_dvd_not_iff_den_two_mul_dvd`.
* `noAdjacent_of_all_even`, `NoAdjacent.subset`, `noAdjacent_insert_even_of_mask`,
  `noAdjacent_union_even_of_mask`, `wordSum_insert`, `wordSum_erase`, `wordSum_union`.
* `Entry` (exact structure), `Entry.height_gt`, `Entry.Q_lt_mem`, `Entry.two_mul_card_le`,
  `Entry.noAdjacent_union_safe`, `noAdjacent_card_bound`, `entryDegenerate`.
* `DescentState`, `DescentStep`, `DescentStep.next_value`, `next_component_lower`, `next_fresh`,
  `descent_terminates`, `descent_normHeight_le`.
* `GuardedReservoir.*`, `positive_mass_not_exact_coverage`.
* `exact_absorption_iff_weight_subsetSum`, `exact_absorption_of_congruence`,
  `fourier_count_identity`, `congCount_pos_of_dominance`.
* `den_dvd_quotient_iff`, `descent_congruence_iff`, `dvd_mul_iff_of_coprime`,
  `dvd_iff_forall_component`, `TransitionSystem.solves_of_independent_repairs`,
  `TransitionSystem.unsolvable_of_common_divisor`, `gcdWitnessSystem_unsolvable`,
  `descentStep_of_congruence`.
* `coset_meets_subgroup_iff`, `mobility_targets_not_hit`.
* `mobility_preserves_doubled_lattice`, `absorber_is_sumset_membership`, `noAdjacent_to_V3_no00`,
  `v4_firewalls_in_force`.
* `final_configuration_is_counterexample`, `no_entry_supply_of_no_counterexample`,
  `OpenOwners.entry_to_original_287_bridge`, `OpenOwners.open_owners`,
  `OpenOwners.false_shortcuts`.

Conditional interfaces (premises explicit, never inhabited):

* `exact_absorption_of_fourier_dominance` — premises: lattice `Δ·P = k`, `n ∣ P` on the reservoir,
  `k < Qm`, total weight `< Qm`, spectral dominance.
* `entry_to_low_height`, `low_height_to_exact_absorb`, `conditional_entry_to_exact_one`,
  `conditional_entry_gives_counterexample` — premises: `Entry`, `DescentSupply`, `AbsorberSupply`.

## 3. Dead routes (do not revive)

* `den(Δ) ∣ P` instead of `den(2Δ) ∣ P` — FALSE (`1/1056 + 1/1080` at `L(30)`).
* `n ∣ L(t) ↔ 𝔥(n) ≤ t` — FALSE (`32`, `t = 16`).
* positive reservoir mass ⇒ exact coverage — FALSE (`{4}`, target `1/8`).
* global column surjectivity / `gcd = 1` ⇒ `0/1` hit — FALSE (effects `{2,3}` mod `7`).
* many mobility targets ⇒ hit — FALSE (four targets mod `8` vs image `{0,4}`).
* rowwise neutrality necessary; many packets ⇒ hit — FALSE (frozen V3 firewalls).

## 4. Exact remaining owners

```
ENTRY_EXISTENCE :
  ∀ M₀, ∃ M aM Q Y, M₀ ≤ M ∧ 2*aM ≤ M ∧ 2*Q ≤ M ∧ Nonempty (Entry M aM Q Y)

SAFE_DESCENT_SUPPLY :
  ∀ aM M Q Y mask, DescentSupply aM M Q Y mask

GUARDED_ABSORBER_ANALYTIC_SUPPLY :
  ∀ aM M Q Y mask, AbsorberSupply aM M Q Y mask
```

`ENTRY_TO_ORIGINAL_287_BRIDGE` is PROVED and needs no further work.

## 5. First next theorem

Prove or refute, for the transition system produced by
`descent_congruence_iff` at the top active height `h` of a candidate interval word:

```
∃ centers ⊆ Finset.Ioo aM M,
  (∀ c ∈ centers, Even c) ∧
  (∀ c ∈ centers, ∀ j, (j = c + 1 ∨ j + 1 = c) → normHeight j ≤ Q) ∧
  Disjoint centers Z ∧
  (r : ℤ) ∣ numeratorAt P S - ∑ n ∈ centers, (weight P n : ℤ)
```

i.e. a single instance of `SAFE_DESCENT_SUPPLY` at one height, with `P = 2 * L h`,
`r = P / (2 * L h')`.  A positive answer, uniform in `h`, discharges `SAFE_DESCENT_SUPPLY`;
a dual certificate from `TransitionSystem.unsolvable_of_common_divisor` for some height refutes it
in the present model.
