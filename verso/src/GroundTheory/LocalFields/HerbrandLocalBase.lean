import Mathlib
import GroundTheory.LocalFields.HerbrandCyclic
import GroundTheory.LocalFields.HilbertCyclic
import GroundTheory.LocalFields.UnitsGalois
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def unitsToTateZero : Kˣ →* TateZero (L ≃ₐ[K] L) Lˣ :=
  (QuotientGroup.mk' _).comp
    ((Units.map (algebraMap K L : K →* L)).codRestrict (invariants (L ≃ₐ[K] L) Lˣ) fun a g => by
      ext
      simp [AlgEquiv.smul_units_def])

/- English proof (translation)
Rewrite using `[algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]`. Both sides reduce to the same expression.
-/
theorem coe_tateNorm_units (x : Lˣ) :
    ((tateNorm (L ≃ₐ[K] L) Lˣ x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  rw [algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]
  rfl

/- English proof (translation)
Introduce `q`. Take `⟨⟨x, hx⟩, rfl⟩` from `QuotientGroup.mk'_surjective _ q`. Establish `hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y` using `fun y hy => (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy`. Take `⟨a, ha⟩` from `hfix (x : L) fun g => congrArg Units.val (hx g)`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero]`. Conclude with `x.ne_zero ha.symm`. Conclude with `⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩`.
-/
theorem unitsToTateZero_surjective : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y := fun y hy =>
    (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  obtain ⟨a, ha⟩ := hfix (x : L) fun g => congrArg Units.val (hx g)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨y, Units.ext ((algebraMap K L).injective ?_)⟩` and prove the remaining obligations.

Rewrite using `[coe_normUnits, ← coe_tateNorm_units, hy]`. Both sides reduce to the same expression. Introduce and unpack `⟨y, rfl⟩`. Use `⟨y, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_tateNorm_units]`.

Both sides reduce to the same expression.
-/
theorem ker_unitsToTateZero : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by
  ext a
  rw [MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ((algebraMap K L).injective ?_)⟩
    rw [coe_normUnits, ← coe_tateNorm_units, hy]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_tateNorm_units]
    rfl

/- English proof (translation)
Rewrite using `[← ker_unitsToTateZero]`. Conclude with `Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm`.
-/
theorem natCard_tateZero_units_eq :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by
  rw [← ker_unitsToTateZero]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm

end Galois

section Ord

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

variable (L) in

def unitsOrd : Additive Lˣ →+ ℤ where
  toFun x := ord ((x.toMul : Lˣ) : L)
  map_zero' := by
    have := ord_unit (K := L) 1
    simpa using this
  map_add' x y := by
    change ord (((x.toMul * y.toMul : Lˣ)) : L) = _
    rw [Units.val_mul, ord_mul x.toMul.ne_zero y.toMul.ne_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitsOrd_ofMul (x : Lˣ) : unitsOrd L (Additive.ofMul x) = ord (x : L) :=
  rfl

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[L]`. Introduce `n`. Use `⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]`.
-/
theorem unitsOrd_surjective : Function.Surjective (unitsOrd L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]`.
-/
theorem ord_eq_zero_iff_mem_range_unitsIncl (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]

/- English proof (translation)
Introduce `y`. Express the relevant statement in the definitionally equal form `ord ((y.toMul : Lˣ) : L) = 0 ↔ _`. Rewrite using `[ord_eq_zero_iff_mem_range_unitsIncl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩`.

Conclude with `⟨Additive.ofMul u, Additive.toMul.injective hu⟩`. Introduce and unpack `⟨u, rfl⟩`. Conclude with `⟨u.toMul, rfl⟩`.
-/
theorem exact_unitsIncl_unitsOrd :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd L) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩

end Ord

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Rewrite using `[ord, ord, normalizedValuation_apply, normalizedValuation_apply, valuation_algEquiv_apply K L σ x]`.
-/
theorem ord_algEquiv (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]

/- English proof (translation)
Rewrite using `[unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]`. Conclude with `ord_algEquiv σ x`.
-/
theorem unitsOrd_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    unitsOrd L (Additive.ofMul (σ • x)) = unitsOrd L (Additive.ofMul x) := by
  rw [unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]
  exact ord_algEquiv σ x

/- English proof (translation)
Rewrite using `[cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]`. Both sides reduce to the same expression.
-/
theorem unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd L (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd L x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl

/- English proof (translation)
Rewrite using `[cycNorm_apply, cycNorm_apply, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]`. Both sides reduce to the same expression.
-/
theorem unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd L (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd L x) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]
  rfl

variable {σ : L ≃ₐ[K] L}

/- English proof (translation)
Establish `hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L))` using `unitsIncl_injective`. Establish `hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ) (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ))` using `hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ`. Establish `hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ) (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L)` using `cyclicHerbrand_trivial_int σ`. Use `⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ) (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩` and prove the remaining obligations. Rewrite using `[cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ) (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]`.

Both sides reduce to the same expression.
-/
theorem cycHerbrand_units_eq_mul (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl

/- English proof (translation)
Establish `: V.subtype.range.FiniteIndex` using `by rw [Subgroup.range_subtype]; infer_instance`. Take `⟨h1, h2⟩` from `cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ`. Take `⟨h3, h4⟩` from `cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ`. Conclude with `⟨h1.mp h3, h2.symm.trans h4⟩`.
-/
theorem cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩

end GroundTheory.LocalField
