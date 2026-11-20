import Mathlib
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.UnitsPowers

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def unitFiltrationUnits (n : ℕ) : Subgroup Kˣ :=
  (unitFiltration K n).map (unitsIncl K)

variable {K}

/- English proof (translation)
The claim follows from `fun _ _ hmn ↦ Subgroup.map_mono (unitFiltration_antitone K hmn)`.
-/
theorem unitFiltrationUnits_antitone : Antitone (unitFiltrationUnits K) :=
  fun _ _ hmn ↦ Subgroup.map_mono (unitFiltration_antitone K hmn)

/- English proof (translation)
Rewrite using `[unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff, ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]`.
-/
theorem mem_unitFiltrationUnits_zero_iff {x : Kˣ} :
    x ∈ unitFiltrationUnits K 0 ↔ valuation K (x : K) = 1 := by
  rw [unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map, mem_range_unitsIncl_iff,
    ← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]

/- English proof (translation)
Establish `hset` using `hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Establish `: ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])` using `hu`. Rewrite `this` using `[hset]`.

Simplify using `using this`. Introduce `h`. Establish `hϖ1 : valuation K (ϖ : K) < 1` using `valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)`. Establish `hlt : valuation K ((x : K) - 1) < 1` using `h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))`. Establish `hx1 : valuation K (x : K) = 1`.

Use `(valuation K).map_one_add_of_lt hlt` as an intermediate fact. Simplify using `using this`. Take `⟨u, rfl⟩` from `mem_range_unitsIncl_iff.mpr (by`. Rewrite using `[← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]`. Conclude with `hx1)`.

Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Use `show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])`. Rewrite using `[hset]`. Simplify using `using h`.
-/
theorem mem_unitFiltrationUnits_iff {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := hu
    rw [hset] at this
    simpa using this
  · intro h
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hlt : valuation K ((x : K) - 1) < 1 :=
      h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))
    have hx1 : valuation K (x : K) = 1 := by
      have := (valuation K).map_one_add_of_lt hlt
      simpa using this
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr (by
      rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]; exact hx1)
    refine ⟨u, ?_, rfl⟩
    show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    rw [hset]
    simpa using h

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩` and prove the remaining obligations. Establish `: z - a = (z - y) + (y - a)` using `by ring`.

Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢`. Rewrite using `[this]`. Conclude with `(valuation K).map_add_le hz.le hy`.
-/
theorem isOpen_setOf_valuation_sub_le {a : K} {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {y : K | valuation K (y - a) ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z - a = (z - y) + (y - a) := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_le hz.le hy

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Establish `hγ : γ ≠ 0` using `ne_bot_of_gt hy`. Use `⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩` and prove the remaining obligations.

Establish `: z = (z - y) + y` using `by ring`. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢`. Rewrite using `[this]`. Conclude with `(valuation K).map_add_lt hz hy`.
-/
theorem isOpen_setOf_valuation_lt {γ : ValueGroupWithZero K} :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  have hγ : γ ≠ 0 := ne_bot_of_gt hy
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  have : z = (z - y) + y := by ring
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz hy ⊢
  rw [this]
  exact (valuation K).map_add_lt hz hy

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨1, fun z hz ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_one] at hz hy ⊢`.

Establish `: z = y + (z - y)` using `by ring`. Rewrite using `[this, (valuation K).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]`.
-/
theorem isOpen_setOf_valuation_eq_one : IsOpen {y : K | valuation K y = 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun z hz ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_one] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation K).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `mem_unitFiltrationUnits_zero_iff.mp hx`. Introduce `hy`.

Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy`. Conclude with `⟨Units.mk0 y hy0, mem_unitFiltrationUnits_zero_iff.mpr hy, rfl⟩`.
-/
theorem val_image_unitFiltrationUnits_zero :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_unitFiltrationUnits_zero_iff.mp hx
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y hy0, mem_unitFiltrationUnits_zero_iff.mpr hy, rfl⟩

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_unitFiltrationUnits_iff hn hϖ).mp hx`. Introduce `hy`.

Establish `hϖ1 : valuation K (ϖ : K) < 1` using `valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Establish `: valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n` using `hy`. Simplify using `only [zero_sub, Valuation.map_neg, map_one] at this`.

Conclude with `(pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this`. Conclude with `⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩`.
-/
theorem val_image_unitFiltrationUnits {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltrationUnits_iff hn hϖ).mp hx
  · intro hy
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n := hy
      simp only [zero_sub, Valuation.map_neg, map_one] at this
      exact (pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this
    exact ⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩

/- English proof (translation)
Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `hϖ.ne_zero` after adjusting the coercions.
-/
theorem valuation_uniformizer_ne_zero {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation K (ϖ : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hϖ.ne_zero

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1}`. Use extensionality with `x`. Conclude with `mem_unitFiltrationUnits_zero_iff`.

Rewrite using `[this]`. Conclude with `isOpen_setOf_valuation_eq_one.preimage Units.continuous_val`. Establish `: (unitFiltrationUnits K n : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n}`. Use extensionality with `x`. Conclude with `mem_unitFiltrationUnits_iff hn hϖ`.

Rewrite using `[this]`. Conclude with `(isOpen_setOf_valuation_sub_le (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val`.
-/
theorem isOpen_unitFiltrationUnits (n : ℕ) : IsOpen (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (unitFiltrationUnits K 0 : Set Kˣ) = (↑) ⁻¹' {y : K | valuation K y = 1} := by
      ext x; exact mem_unitFiltrationUnits_zero_iff
    rw [this]
    exact isOpen_setOf_valuation_eq_one.preimage Units.continuous_val
  · have : (unitFiltrationUnits K n : Set Kˣ) =
        (↑) ⁻¹' {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
      ext x; exact mem_unitFiltrationUnits_iff hn hϖ
    rw [this]
    exact (isOpen_setOf_valuation_sub_le
      (pow_ne_zero _ (valuation_uniformizer_ne_zero hϖ))).preimage Units.continuous_val

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Rewrite using `[Units.isEmbedding_val₀.isCompact_iff]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Rewrite using `[val_image_unitFiltrationUnits_zero]`. Establish `: {y : K | valuation K y = 1} = {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1}`.

Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨h.le, h.ge⟩`.

Introduce `h`. Conclude with `le_antisymm h.1 h.2`. Rewrite using `[this]`. Conclude with `(IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt`. Rewrite using `[val_image_unitFiltrationUnits hn hϖ]`.

Establish `: {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} = (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n}`. Use extensionality with `y`. Both sides reduce to the same expression. Rewrite using `[this, Homeomorph.isCompact_preimage]`. Conclude with `IsNonarchimedeanLocalField.isCompact_closedBall K _`.
-/
theorem isCompact_unitFiltrationUnits (n : ℕ) : IsCompact (unitFiltrationUnits K n : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [val_image_unitFiltrationUnits_zero]
    have : {y : K | valuation K y = 1} =
        {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
      constructor
      · intro h; exact ⟨h.le, h.ge⟩
      · intro h; exact le_antisymm h.1 h.2
    rw [this]
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff isOpen_setOf_valuation_lt
  · rw [val_image_unitFiltrationUnits hn hϖ]
    have : {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} =
        (Homeomorph.subRight (1 : K)) ⁻¹' {y : K | valuation K y ≤ valuation K (ϖ : K) ^ n} := by
      ext y; rfl
    rw [this, Homeomorph.isCompact_preimage]
    exact IsNonarchimedeanLocalField.isCompact_closedBall K _

/- English proof (translation)
Take `⟨z, rfl⟩` from `ValuativeRel.valuation_surjective γ`. Establish `hz : z ≠ 0` using `by rintro rfl; simp at hγ`. Use `⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ, normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]`. Simplify using `only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]`.

Use `le_max_right 1 (ord z + 1).toNat` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_pow_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    ∃ n, 1 ≤ n ∧ valuation K (ϖ : K) ^ n < γ := by
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hz : z ≠ 0 := by rintro rfl; simp at hγ
  refine ⟨max 1 (ord z + 1).toNat, le_max_left _ _, ?_⟩
  rw [← map_pow, ← normalizedValuation_lt_iff, map_pow, normalizedValuation_uniformizer hϖ,
    normalizedValuation_eq_exp_ord hz, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
  simp only [nsmul_eq_mul, mul_neg, mul_one, neg_lt_neg_iff]
  have := le_max_right 1 (ord z + 1).toNat
  omega

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Rewrite using `[Filter.hasBasis_iff]`. Introduce `t`. Prove the components needed by the constructor for the conclusion. Introduce `ht`.

Rewrite `ht` using `[Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap]`. Take `⟨t', ht', hsub⟩` from `ht`. Rewrite `ht'` using `[Units.val_one, IsValuativeTopology.mem_nhds_iff']`. Take `⟨γ, hγ⟩` from `ht'`. Take `⟨n, hn, hlt⟩` from `exists_pow_lt hϖ γ.ne_zero`.

Use `⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩` and prove the remaining obligations. Conclude with `((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt`. Introduce and unpack `⟨n, -, hn⟩`. Conclude with `Filter.mem_of_superset ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn`.
-/
theorem hasBasis_nhds_one_unitFiltrationUnits :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ ↦ True) (fun n ↦ (unitFiltrationUnits K n : Set Kˣ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨t', ht', hsub⟩ := ht
    rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    obtain ⟨n, hn, hlt⟩ := exists_pow_lt hϖ γ.ne_zero
    refine ⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩
    exact ((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn

/- English proof (translation)
Take `⟨n, -, hn⟩` from `hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp (hH.mem_nhds (Subgroup.one_mem H))`. Conclude with `⟨n, hn⟩`.
-/
theorem exists_unitFiltrationUnits_le {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) :
    ∃ n, unitFiltrationUnits K n ≤ H := by
  obtain ⟨n, -, hn⟩ :=
    hasBasis_nhds_one_unitFiltrationUnits.mem_iff.mp (hH.mem_nhds (Subgroup.one_mem H))
  exact ⟨n, hn⟩

/- English proof (translation)
Use `⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `H.pow_index_mem x`.
-/
theorem exists_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex] :
    ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H := by
  refine ⟨H.index, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact H.pow_index_mem x

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩`.
-/
theorem exists_unitFiltrationUnits_le_and_range_pow_le {H : Subgroup Kˣ} [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    (∃ n, unitFiltrationUnits K n ≤ H) ∧ ∃ m, m ≠ 0 ∧ (powMonoidHom m : Kˣ →* Kˣ).range ≤ H :=
  ⟨exists_unitFiltrationUnits_le hH, exists_range_pow_le⟩

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_unitFiltration_le_range_pow hm`. Use `Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Take `⟨x, rfl⟩` from `hN hu`. Conclude with `⟨unitsIncl K x, by simp⟩`.
-/
theorem isOpen_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom m : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  refine Subgroup.isOpen_mono ?_ (isOpen_unitFiltrationUnits N)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, rfl⟩ := hN hu
  exact ⟨unitsIncl K x, by simp⟩

end GroundTheory.LocalField
