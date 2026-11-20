import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerLocalDefs
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SumInvariants
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.CupDecompositionGlobal
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplitLayers
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section TowerInfl

variable {k L : Type} [Field k] [Field L] [Algebra k L] [IsGalois k L] (M : IntermediateField k L)
  [Normal k M]

/- English proof (translation)
Establish `: Algebra.IsSeparable k M` using `Algebra.isSeparable_tower_bot_of_isSeparable k M L`. Establish `: IsGalois k M` using `⟨⟩`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨E, y, rfl⟩` from `exists_unitsInflation_eq (K := k) (L := M) 2 x`.

Set `E₀ : IntermediateField k M` to `E.toIntermediateField`. Set `E' : IntermediateField k L` to `E₀.map M.val`. Set `e : E₀ ≃ₐ[k] E'` to `E₀.equivMap M.val`. Set `_ : Algebra E₀ E'` to `e.toRingHom.toAlgebra`. Establish `: IsScalarTower k E₀ E'` using `IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm`.

Establish `: FiniteDimensional k E'` using `e.toLinearEquiv.finiteDimensional`. Establish `: Normal k E'` using `Normal.of_algEquiv e`. Establish `: Algebra.IsSeparable k E'` using `Algebra.isSeparable_tower_bot_of_isSeparable k E' L`. Establish `: IsGalois k E'` using `⟨⟩`. Establish `hg : ∀ σ : Gal(L/k), AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M σ) = AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' σ)`.

Introduce `σ`. Establish `hE : ∀ z : E₀, ((algebraMap E₀ E' z : E') : L) = ((z : M) : L)` using `fun z => rfl`. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `a`. Apply `Subtype.val_injective` to reduce the goal to its premises.

Apply `Subtype.val_injective` to reduce the goal to its premises. Establish `l1` using `AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom M σ) E₀ a`. Establish `l2` using `AlgEquiv.restrictNormal_commutes σ M (a : M)`. Establish `r1` using `AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom E' σ) E₀ a`. Establish `r2` using `AlgEquiv.restrictNormal_commutes σ E' (algebraMap E₀ E' a)`.

Combine the equalities or inequalities in the displayed calculation. Establish `key : unitsInflation E₀ 2 ≫ cohomologyMapAlong (AlgEquiv.restrictNormalHom M) (InfiniteGalois.restrictNormalHom_continuous M) (unitsRestrictHom M) 2 = unitsInflationTower k E₀ E' 2 ≫ unitsInflation E' 2`. Unfold `unitsInflation unitsInflationTower groupCohomology.map cohomologyMapAlong`. Use `erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]`. Use `congr 1`.

Use extensionality with `n : 1`. Rewrite using `[← cancel_mono ((cochainsComplexι (galUnits k L)).f n), HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc]`. Use extensionality with `c : 2`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `(unitsRestrictHom M).hom ((unitsRestrictHom E₀).hom (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M (g i)))) = (unitsRestrictHom E').hom ((unitsTowerHom k E₀ E').hom (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' (g i))))`.

Simplify using `only [hg]`. Conclude with `Additive.toMul.injective (Units.ext rfl)`. Establish `h1 : (unitsInflation E' 2).hom ((unitsInflationTower k E₀ E' 2).hom y) = 0`. Rewrite using `[← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← key, ModuleCat.hom_comp, LinearMap.comp_apply]`. Conclude with `hx`.

Establish `h2` using `brauerInflation_injective E' (h1.trans (map_zero _).symm)`. Establish `h3` using `unitsInflationTower_two_injective k E₀ E' (h2.trans (map_zero _).symm)`. Rewrite using `[h3, map_zero]`.
-/
theorem cohomologyMapAlong_restrictNormalHom_two_injective :
    Function.Injective (cohomologyMapAlong (AlgEquiv.restrictNormalHom M)
      (InfiniteGalois.restrictNormalHom_continuous M) (unitsRestrictHom M) 2).hom := by
  have : Algebra.IsSeparable k M := Algebra.isSeparable_tower_bot_of_isSeparable k M L
  have : IsGalois k M := ⟨⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨E, y, rfl⟩ := exists_unitsInflation_eq (K := k) (L := M) 2 x
  let E₀ : IntermediateField k M := E.toIntermediateField
  let E' : IntermediateField k L := E₀.map M.val
  let e : E₀ ≃ₐ[k] E' := E₀.equivMap M.val
  let _ : Algebra E₀ E' := e.toRingHom.toAlgebra
  have : IsScalarTower k E₀ E' := IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  have : FiniteDimensional k E' := e.toLinearEquiv.finiteDimensional
  have : Normal k E' := Normal.of_algEquiv e
  have : Algebra.IsSeparable k E' := Algebra.isSeparable_tower_bot_of_isSeparable k E' L
  have : IsGalois k E' := ⟨⟩
  have hg : ∀ σ : Gal(L/k), AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M σ) =
      AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' σ) := by
    intro σ
    have hE : ∀ z : E₀, ((algebraMap E₀ E' z : E') : L) = ((z : M) : L) := fun z => rfl
    apply AlgEquiv.ext
    intro a
    apply Subtype.val_injective
    apply Subtype.val_injective
    have l1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom M σ) E₀ a
    have l2 := AlgEquiv.restrictNormal_commutes σ M (a : M)
    have r1 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictNormalHom E' σ) E₀ a
    have r2 := AlgEquiv.restrictNormal_commutes σ E' (algebraMap E₀ E' a)
    calc (((AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M σ) a : E₀) : M) : L)
        = ((AlgEquiv.restrictNormalHom M σ (a : M) : M) : L) := congrArg Subtype.val l1
      _ = σ ((a : M) : L) := l2
      _ = σ ((algebraMap E₀ E' a : E') : L) := by rw [hE]
      _ = ((AlgEquiv.restrictNormalHom E' σ (algebraMap E₀ E' a) : E') : L) := r2.symm
      _ = ((algebraMap E₀ E' (AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' σ) a) : E') :
          L) := congrArg Subtype.val r1.symm
      _ = _ := hE _
  have key : unitsInflation E₀ 2 ≫ cohomologyMapAlong (AlgEquiv.restrictNormalHom M)
      (InfiniteGalois.restrictNormalHom_continuous M) (unitsRestrictHom M) 2 =
      unitsInflationTower k E₀ E' 2 ≫ unitsInflation E' 2 := by
    unfold unitsInflation unitsInflationTower groupCohomology.map cohomologyMapAlong
    erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    ext n : 1
    rw [← cancel_mono ((cochainsComplexι (galUnits k L)).f n), HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, Category.assoc, Category.assoc]
    ext c : 2
    funext g
    change (unitsRestrictHom M).hom ((unitsRestrictHom E₀).hom
        (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom M (g i)))) =
      (unitsRestrictHom E').hom ((unitsTowerHom k E₀ E').hom
        (c fun i => AlgEquiv.restrictNormalHom E₀ (AlgEquiv.restrictNormalHom E' (g i))))
    simp only [hg]
    exact Additive.toMul.injective (Units.ext rfl)
  have h1 : (unitsInflation E' 2).hom ((unitsInflationTower k E₀ E' 2).hom y) = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← key, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hx
  have h2 := brauerInflation_injective E' (h1.trans (map_zero _).symm)
  have h3 := unitsInflationTower_two_injective k E₀ E' (h2.trans (map_zero _).symm)
  rw [h3, map_zero]

end TowerInfl

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

instance isDiscreteRep_uliftIntToIntRep_galUnits_algebraicClosure :
    IsDiscreteRep (uliftIntToIntRep (galUnits K.1 ℚ̄)) :=
  isDiscreteRep_uliftIntToIntRep _

def galToFixing : Gal(ℚ̄/K.1) →* K.1.fixingSubgroup :=
  (IntermediateField.fixingSubgroupEquiv K.1).symm.toMonoidHom

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 (continuous_restrictScalarsHom_of_tower ℚ K.1 ℚ̄)`.
-/
theorem continuous_galToFixing : Continuous (galToFixing K) :=
  continuous_induced_rng.2 (continuous_restrictScalarsHom_of_tower ℚ K.1 ℚ̄)

def galToFixingUnitsMor :
    Rep.res (galToFixing K) (unitsLimitRep K) ⟶ uliftIntToIntRep (galUnits K.1 ℚ̄) :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive ℚ̄ˣ)).toIntLinearMap, fun _ => rfl⟩

def maxUnitsRestrictMor :
    Rep.res (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
        (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) ⟶
      uliftIntToIntRep (galUnits K.1 ℚ̄) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext
      (AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K.1 ℚ̄ S)
        ((Additive.toMul (α := (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) x :
          (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)))⟩

/- English proof (translation)
Use `MonoidHom.ext fun σ => AlgEquiv.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Conclude with `(gsRestrict_apply K S (galToFixing K σ) y).trans (AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K.1 ℚ̄ S) y).symm`.
-/
theorem gsRestrict_comp_galToFixing :
    (gsRestrict K S).comp (galToFixing K) =
      AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S) := by
  refine MonoidHom.ext fun σ => AlgEquiv.ext fun y => Subtype.ext ?_
  exact (gsRestrict_apply K S (galToFixing K σ) y).trans
    (AlgEquiv.restrictNormal_commutes σ (maxUnramifiedOutside K.1 ℚ̄ S) y).symm

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨x', rfl⟩` from `(cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).surjective x`. It suffices to establish `h : (cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S)) (InfiniteGalois.restrictNormalHom_continuous _) (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom x' = 0 by`. Rewrite using `[cohomologyMapAlong_restrictNormalHom_two_injective _ (h.trans (map_zero _).symm), map_zero]`.

Apply `(cohomologyULiftIntAddEquiv (galUnits K.1 ℚ̄) 2).injective` to reduce the goal to its premises. Rewrite using `[map_zero, cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S)) (InfiniteGalois.restrictNormalHom_continuous _) (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S)) (maxUnitsRestric …`. Establish `e : cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S)) (InfiniteGalois.restrictNormalHom_continuous _) (maxUnitsRestrictMor K S) 2 = gsBrauerInfl K S 2 ≫ cohomologyMapAlong (galToFixing K) (continuous_galToFixing K) (galToFixingUnitsMor K) 2`. Rewrite using `[gsBrauerInfl, ← cohomologyMapAlong_comp]`. Conclude with `cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_galToFixing K S).symm (fun _ => rfl) 2`.

Rewrite using `[e, ConcreteCategory.comp_apply, hx, map_zero]`.
-/
theorem gsBrauerInfl_injective : Function.Injective (gsBrauerInfl K S 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x', rfl⟩ :=
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).surjective x
  suffices h : (cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
      (InfiniteGalois.restrictNormalHom_continuous _)
      (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S)) 2).hom x' = 0 by
    rw [cohomologyMapAlong_restrictNormalHom_two_injective _ (h.trans (map_zero _).symm), map_zero]
  apply (cohomologyULiftIntAddEquiv (galUnits K.1 ℚ̄) 2).injective
  rw [map_zero, cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))
    (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
    (InfiniteGalois.restrictNormalHom_continuous _) (unitsRestrictHom (maxUnramifiedOutside K.1 ℚ̄ S))
    (maxUnitsRestrictMor K S) (fun _ => rfl) 2 x']
  have e : cohomologyMapAlong (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S))
      (InfiniteGalois.restrictNormalHom_continuous _) (maxUnitsRestrictMor K S) 2 =
      gsBrauerInfl K S 2 ≫ cohomologyMapAlong (galToFixing K) (continuous_galToFixing K)
        (galToFixingUnitsMor K) 2 := by
    rw [gsBrauerInfl, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_galToFixing K S).symm (fun _ => rfl) 2
  rw [e, ConcreteCategory.comp_apply, hx, map_zero]

section Local

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

/- English proof (translation)
Use `MonoidHom.ext fun σ => ((decompHom_eq_iff _ σ _).2 fun y => ?_).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (((gsRestrict K S (globalDecomp (v.adicCompletion K.1) ι σ) y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) = σ (ι (y : ℚ̄))`. Rewrite using `[gsRestrict_apply]`. Conclude with `globalDecomp_apply _ ι σ y`.
-/
theorem gsRestrict_comp_globalDecomp :
    (gsRestrict K S).comp (globalDecomp (v.adicCompletion K.1) ι) =
      decompHomS (v.adicCompletion K.1) S ι := by
  refine MonoidHom.ext fun σ => ((decompHom_eq_iff _ σ _).2 fun y => ?_).symm
  change ι (((gsRestrict K S (globalDecomp (v.adicCompletion K.1) ι σ) y :
    maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) = σ (ι (y : ℚ̄))
  rw [gsRestrict_apply]
  exact globalDecomp_apply _ ι σ y

/- English proof (translation)
The claim follows from `Additive.toMul.injective (Units.ext rfl)`.
-/
theorem gsUnitsMor_comp_unitsLocalMor_hom_apply (a : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
    ((Rep.resFunctor (globalDecomp (v.adicCompletion K.1) ι)).map (gsUnitsMor K S) ≫
      unitsLocalMor (v.adicCompletion K.1) ι).hom a = (embUnitsMorZ S ι).hom a :=
  Additive.toMul.injective (Units.ext rfl)

/- English proof (translation)
Rewrite using `[gsBrauerInfl, unitsLocalRes, ← cohomologyMapAlong_comp, gsLocalRes]`. Conclude with `cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_globalDecomp K S ι) (gsUnitsMor_comp_unitsLocalMor_hom_apply K S ι) n`.
-/
theorem gsBrauerInfl_comp_unitsLocalRes (n : ℕ) :
    gsBrauerInfl K S n ≫ unitsLocalRes (v.adicCompletion K.1) ι n = gsLocalRes S ι n := by
  rw [gsBrauerInfl, unitsLocalRes, ← cohomologyMapAlong_comp, gsLocalRes]
  exact cohomologyMapAlong_congr _ _ _ _ (gsRestrict_comp_globalDecomp K S ι)
    (gsUnitsMor_comp_unitsLocalMor_hom_apply K S ι) n

end Local

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Rewrite using `[brauerLocal_apply_inr, ← ConcreteCategory.comp_apply, gsBrauerInfl_comp_unitsLocalRes]`.
-/
theorem brauerLocal_gsBrauerInfl_inr (ιs : LocalEmbeddings K) (v : HeightOneSpectrum (𝓞 K.1))
    (x : cohomology (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))) 2) :
    brauerLocal ιs ((gsBrauerInfl K S 2).hom x) (.inr v) = (gsLocalRes S (ιs.fin v) 2).hom x := by
  rw [brauerLocal_apply_inr, ← ConcreteCategory.comp_apply, gsBrauerInfl_comp_unitsLocalRes]

section Descent

def gsLift (τ : galUnramifiedOutside K.1 ℚ̄ S) : K.1.fixingSubgroup :=
  galToFixing K (τ.liftNormal ℚ̄)

/- English proof (translation)
Introduce `τ`. Use `AlgEquiv.ext fun y => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[gsRestrict_apply]`. Conclude with `AlgEquiv.liftNormal_commutes τ ℚ̄ y`.
-/
theorem gsRestrict_gsLift : Function.RightInverse (gsLift K S) (gsRestrict K S) := by
  intro τ
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  rw [gsRestrict_apply]
  exact AlgEquiv.liftNormal_commutes τ ℚ̄ y

variable (E : FiniteSubfield) [Fact (K ≤ E)] [IsGalois K.1 E.1]

abbrev fixingSubgroupOf : Subgroup K.1.fixingSubgroup :=
  E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup

instance normal_fixingSubgroupOf : (fixingSubgroupOf K E).Normal :=
  normal_subgroupOf_of_isGalois (K := K) (E := E)

variable {E}

/- English proof (translation)
Introduce `σ hσ`. Rewrite using `[QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `h` using `congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S => ((τ ⟨x, hE x hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) (MonoidHom.mem_ker.1 hσ)`. Rewrite `h` using `[gsRestrict_apply]`.

Conclude with `h`.
-/
theorem ker_gsRestrict_le (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    (gsRestrict K S).ker ≤ (QuotientGroup.mk' (fixingSubgroupOf K E)).ker := by
  intro σ hσ
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h := congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S =>
    ((τ ⟨x, hE x hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) (MonoidHom.mem_ker.1 hσ)
  rw [gsRestrict_apply] at h
  exact h

def gsToQuotient (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    galUnramifiedOutside K.1 ℚ̄ S →* K.1.fixingSubgroup ⧸ fixingSubgroupOf K E :=
  (gsRestrict K S).liftOfRightInverse (gsLift K S) (gsRestrict_gsLift K S)
    ⟨QuotientGroup.mk' (fixingSubgroupOf K E), ker_gsRestrict_le K S hE⟩

/- English proof (translation)
The claim follows from `MonoidHom.liftOfRightInverse_comp _ _ _ _`.
-/
theorem gsToQuotient_comp (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    (gsToQuotient K S hE).comp (gsRestrict K S) = QuotientGroup.mk' (fixingSubgroupOf K E) :=
  MonoidHom.liftOfRightInverse_comp _ _ _ _

/- English proof (translation)
Establish `: T2Space (galUnramifiedOutside K.1 ℚ̄ S)` using `galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)`. Establish `hq : Topology.IsQuotientMap (gsRestrict K S)` using `((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S) (gsRestrict_gsLift K S).surjective`. Rewrite using `[hq.continuous_iff]`. Express the relevant statement in the definitionally equal form `Continuous ((gsToQuotient K S hE).comp (gsRestrict K S))`. Rewrite using `[gsToQuotient_comp]`.

Conclude with `continuous_quotientGroup_mk' _`.
-/
theorem continuous_gsToQuotient (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Continuous (gsToQuotient K S hE) := by
  have : T2Space (galUnramifiedOutside K.1 ℚ̄ S) := galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  have hq : Topology.IsQuotientMap (gsRestrict K S) :=
    ((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S)
      (gsRestrict_gsLift K S).surjective
  rw [hq.continuous_iff]
  change Continuous ((gsToQuotient K S hE).comp (gsRestrict K S))
  rw [gsToQuotient_comp]
  exact continuous_quotientGroup_mk' _

instance isDiscreteRep_quotientToInvariants_fixingSubgroupOf :
    IsDiscreteRep ((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

variable (E) in

abbrev unitsInvariantsOf :=
  Representation.invariants ((unitsLimitRep K).ρ.comp (fixingSubgroupOf K E).subtype)

omit [IsGalois K.1 E.1] in

/- English proof (translation)
Establish `: IsGalois ℚ ℚ̄` using `IsAlgClosure.isGalois ℚ ℚ̄`. Use `hE _ ?_` and prove the remaining obligations. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup E.1, IntermediateField.mem_fixedField_iff]`. Introduce `g hg`. Establish `hK : g ∈ K.1.fixingSubgroup` using `IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E) hg`.

Establish `h` using `a.2 ⟨⟨g, hK⟩, Subgroup.mem_subgroupOf.2 hg⟩`. Conclude with `congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) h`.
-/
theorem mem_of_mem_invariants (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (a : unitsInvariantsOf K E) :
    (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  refine hE _ ?_
  rw [← InfiniteGalois.fixedField_fixingSubgroup E.1, IntermediateField.mem_fixedField_iff]
  intro g hg
  have hK : g ∈ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E) hg
  have h := a.2 ⟨⟨g, hK⟩, Subgroup.mem_subgroupOf.2 hg⟩
  exact congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) h

def invariantsToMaxUnitsFun (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    unitsInvariantsOf K E →+ Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ where
  toFun a := Additive.ofMul (Units.mk0
      (⟨(((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄), mem_of_mem_invariants K S hE a⟩ :
        maxUnramifiedOutside K.1 ℚ̄ S)
      (fun h => (Additive.toMul (a : Additive ℚ̄ˣ)).ne_zero (congrArg Subtype.val h)))
  map_zero' := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

omit [IsGalois K.1 E.1] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_invariantsToMaxUnitsFun (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (a : unitsInvariantsOf K E) :
    ((((Additive.toMul (invariantsToMaxUnitsFun K S hE a)) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_quotientToInvariants_mk (σ : K.1.fixingSubgroup) (a : unitsInvariantsOf K E) :
    (((Additive.toMul ((((unitsLimitRep K).ρ.quotientToInvariants (fixingSubgroupOf K E))
      (QuotientGroup.mk σ) a : unitsInvariantsOf K E) : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) =
      (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

/- English proof (translation)
Establish `hτ` using `gsRestrict_gsLift K S τ`. Establish `h1 : gsToQuotient K S hE τ = QuotientGroup.mk (gsLift K S τ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h2` using `gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_of_mem_invariants K S hE a⟩`. Rewrite `h2` using `[hτ]`. Conclude with `h2.symm`.
-/
theorem invariantsToMaxUnitsFun_smul (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (τ : galUnramifiedOutside K.1 ℚ̄ S) (a : unitsInvariantsOf K E) :
    invariantsToMaxUnitsFun K S hE
        ((((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)).ρ (gsToQuotient K S hE τ)) a) =
      (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))).ρ τ
        (invariantsToMaxUnitsFun K S hE a) := by
  have hτ := gsRestrict_gsLift K S τ
  have h1 : gsToQuotient K S hE τ = QuotientGroup.mk (gsLift K S τ) := by
    calc gsToQuotient K S hE τ = gsToQuotient K S hE (gsRestrict K S (gsLift K S τ)) := by rw [hτ]
      _ = QuotientGroup.mk (gsLift K S τ) := DFunLike.congr_fun (gsToQuotient_comp K S hE) _
  rw [h1]
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have h2 := gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_of_mem_invariants K S hE a⟩
  rw [hτ] at h2
  exact h2.symm

def invariantsToMaxUnits (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Rep.res (gsToQuotient K S hE) ((unitsLimitRep K).quotientToInvariants (fixingSubgroupOf K E)) ⟶
      uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(invariantsToMaxUnitsFun K S hE).toIntLinearMap, fun τ =>
    LinearMap.ext fun a => invariantsToMaxUnitsFun_smul K S hE τ a⟩

/- English proof (translation)
Rewrite using `[gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]`. Use `cohomologyMapAlong_congr _ _ _ _ (gsToQuotient_comp K S hE) (fun a => ?_) 2` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `coe_invariantsToMaxUnitsFun K S hE a`.
-/
theorem invariantsToMaxUnits_comp_gsBrauerInfl (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    cohomologyMapAlong (gsToQuotient K S hE) (continuous_gsToQuotient K S hE)
      (invariantsToMaxUnits K S hE) 2 ≫ gsBrauerInfl K S 2 =
      cohomologyInfl (unitsLimitRep K) (fixingSubgroupOf K E) 2 := by
  rw [gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]
  refine cohomologyMapAlong_congr _ _ _ _ (gsToQuotient_comp K S hE) (fun a => ?_) 2
  apply Additive.toMul.injective
  apply Units.ext
  exact coe_invariantsToMaxUnitsFun K S hE a

/- English proof (translation)
Establish `hN : IsClosed ((fixingSubgroupOf K E : Subgroup K.1.fixingSubgroup) : Set K.1.fixingSubgroup)` using `Subgroup.isClosed_of_isOpen _ isOpen_subgroupOf_fixingSubgroup`. Establish `hex` using `(infRes_exact (unitsLimitRep K) (fixingSubgroupOf K E) hN (q := 2) two_ne_zero fun i hi0 hi2 => by`. Take `rfl : i = 1` from `by omega`. Conclude with `isZero_cohomology_one_res_subgroupOf).2`. Establish `hmem : x ∈ LinearMap.range (cohomologyInfl (unitsLimitRep K) (fixingSubgroupOf K E) 2).hom`.

Rewrite using `[hex, LinearMap.mem_ker]`. Conclude with `(unitsResField_eq_zero_iff 2 x).1 hx`. Take `⟨z, rfl⟩` from `hmem`. Use `⟨(cohomologyMapAlong (gsToQuotient K S hE) (continuous_gsToQuotient K S hE) (invariantsToMaxUnits K S hE) 2).hom z, ?_⟩` and prove the remaining obligations. Rewrite using `[← ConcreteCategory.comp_apply, invariantsToMaxUnits_comp_gsBrauerInfl]`.
-/
theorem exists_gsBrauerInfl_eq_of_unitsResField_eq_zero
    (hE : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (x : cohomology (unitsLimitRep K) 2)
    (hx : (unitsResField K E 2).hom x = 0) : ∃ y, (gsBrauerInfl K S 2).hom y = x := by
  have hN : IsClosed ((fixingSubgroupOf K E : Subgroup K.1.fixingSubgroup) : Set K.1.fixingSubgroup) :=
    Subgroup.isClosed_of_isOpen _ isOpen_subgroupOf_fixingSubgroup
  have hex := (infRes_exact (unitsLimitRep K) (fixingSubgroupOf K E) hN (q := 2) two_ne_zero
    fun i hi0 hi2 => by
      obtain rfl : i = 1 := by omega
      exact isZero_cohomology_one_res_subgroupOf).2
  have hmem : x ∈ LinearMap.range (cohomologyInfl (unitsLimitRep K) (fixingSubgroupOf K E) 2).hom := by
    rw [hex, LinearMap.mem_ker]
    exact (unitsResField_eq_zero_iff 2 x).1 hx
  obtain ⟨z, rfl⟩ := hmem
  refine ⟨(cohomologyMapAlong (gsToQuotient K S hE) (continuous_gsToQuotient K S hE)
    (invariantsToMaxUnits K S hE) 2).hom z, ?_⟩
  rw [← ConcreteCategory.comp_apply, invariantsToMaxUnits_comp_gsBrauerInfl]

end Descent

section Split

variable {K S}

/- English proof (translation)
Rewrite using `[unitsResField, unitsResField, ← cohomologyMapAlong_comp, unitsResField]`. Conclude with `cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n`.
-/
theorem unitsResField_comp_unitsResField {E M : FiniteSubfield} [Fact (K ≤ E)] [Fact (E ≤ M)]
    [Fact (K ≤ M)] (n : ℕ) : unitsResField K E n ≫ unitsResField E M n = unitsResField K M n := by
  rw [unitsResField, unitsResField, ← cohomologyMapAlong_comp, unitsResField]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

/- English proof (translation)
Introduce `v hv h`. Rewrite `h` using `[Nat.cast_pow]`. Conclude with `hv (hS v (v.isPrime.mem_of_pow_mem _ h))`.
-/
theorem natCast_pow_not_mem_of_forall {ℓ : ℕ}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (b : ℕ) :
    ∀ v ∉ S, (((ℓ ^ b : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := by
  intro v hv h
  rw [Nat.cast_pow] at h
  exact hv (hS v (v.isPrime.mem_of_pow_mem _ h))

/- English proof (translation)
Establish `hle : Cyclotomic.rootsOfUnityField (ℓ ^ b) ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ` using `IntermediateField.adjoin_le_iff.2 fun y hy => mem_maxUnramifiedOutside_of_pow_eq_one S (pow_ne_zero _ hℓ.ne_zero) (natCast_pow_not_mem_of_forall hS b) hy`. Conclude with `fun x hx => hle hx`.
-/
theorem mem_maxUnramifiedOutside_of_mem_rootsOfUnityField {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (b : ℕ) :
    ∀ x ∈ Cyclotomic.rootsOfUnityField (ℓ ^ b), x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have hle : Cyclotomic.rootsOfUnityField (ℓ ^ b) ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 fun y hy =>
      mem_maxUnramifiedOutside_of_pow_eq_one S (pow_ne_zero _ hℓ.ne_zero)
        (natCast_pow_not_mem_of_forall hS b) hy
  exact fun x hx => hle hx

/- English proof (translation)
Establish `hle : (CyclotomicSymbol.compositum K F).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ` using `sup_le (fun x hx => (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨x, hx⟩ : K.1)) fun x hx => hF x hx`. Conclude with `fun x hx => hle hx`.
-/
theorem mem_maxUnramifiedOutside_of_mem_compositum {F : FiniteSubfield}
    (hF : ∀ x ∈ F.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    ∀ x ∈ (CyclotomicSymbol.compositum K F).1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have hle : (CyclotomicSymbol.compositum K F).1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ :=
    sup_le (fun x hx => (maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨x, hx⟩ : K.1)) fun x hx => hF x hx
  exact fun x hx => hle hx

/- English proof (translation)
Use `IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin ℚ _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y ^ ℓ ^ b = 1`. Express the relevant statement in the definitionally equal form `y ^ ℓ ^ a = 1 at hy`. Take `⟨c, hc⟩` from `pow_dvd_pow ℓ hab`. Rewrite using `[hc, pow_mul, hy, one_pow]`.
-/
theorem rootsOfUnityField_pow_le {ℓ : ℕ} {a b : ℕ} (hab : a ≤ b) :
    Cyclotomic.rootsOfUnityField (ℓ ^ a) ≤ Cyclotomic.rootsOfUnityField (ℓ ^ b) := by
  refine IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin ℚ _ ?_
  change y ^ ℓ ^ b = 1
  change y ^ ℓ ^ a = 1 at hy
  obtain ⟨c, hc⟩ := pow_dvd_pow ℓ hab
  rw [hc, pow_mul, hy, one_pow]

end Split

/- English proof (translation)
Establish `hℓ2 : 2 < ℓ ^ 2` using `by nlinarith [hℓ.two_le]`. Establish `: NeZero (ℓ ^ 2)` using `⟨pow_ne_zero _ hℓ.ne_zero⟩`. Set `F₂ : FiniteSubfield` to `⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩`. Set `K' : FiniteSubfield` to `CyclotomicSymbol.compositum K F₂`. Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`.

Establish `: Fact (F₂ ≤ K')` using `CyclotomicSymbol.fact_le_compositum_right K F₂`. Establish `: IsTotallyComplex F₂.1` using `IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2`. Set `_ : Algebra F₂.1 K'.1` to `FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ K')`. Establish `: IsTotallyComplex K'.1` using `NumberField.isTotallyComplex_of_algebra (F := F₂.1) K'.1`. Take `⟨ι'⟩` from `nonempty_localEmbeddings K'`.

Use `set x' := (unitsResField K K' 2).hom x with hx'`. Establish `hm : (ℓ ^ k) • x' = 0` using `by rw [hx', ← map_nsmul, hx, map_zero]`. Set `T : Finset (HeightOneSpectrum (𝓞 K'.1))` to `(brauerLocal ι' x').support.preimage Sum.inr Sum.inr_injective.injOn`. Take `⟨r, ⟨N, hr⟩, hdeg⟩` from `CyclotomicLayer.exists_pow_dvd_finrank_cyclotomicLayer K' T (pow_ne_zero k hℓ.ne_zero)`. Set `E' : FiniteSubfield` to `CyclotomicLayer.cyclotomicLayer K' r`.

Establish `hsplit : (unitsResField K' E' 2).hom x' = 0`. Use `unitsResField_eq_zero_of_dvd_finrank ι' x' (ℓ ^ k) hm (fun v => ?_) fun v hv w => ?_` and prove the remaining obligations. Use `subsingleton_cohomology_two_of_isComplex v (IsTotallyComplex.isComplex v)` as an intermediate fact. Conclude with `Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _`. Conclude with `hdeg v (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact hv) w`.

Set `a` to `k * (N + 1)`. Set `b` to `a + Cyclotomic.unitsLevel ℓ + 2`. Establish `: NeZero (ℓ ^ b)` using `⟨pow_ne_zero _ hℓ.ne_zero⟩`. Set `F : FiniteSubfield` to `⟨Cyclotomic.rootsOfUnityField (ℓ ^ b), inferInstance⟩`. Set `E : FiniteSubfield` to `CyclotomicSymbol.compositum K F`.

Establish `hrq : r = Cyclotomic.primePowPNat ℓ a`. Apply `PNat.eq` to reduce the goal to its premises. Rewrite using `[hr, Cyclotomic.coe_primePowPNat, ← pow_mul]`. Establish `hF₂F : F₂.1 ≤ F.1` using `rootsOfUnityField_pow_le (by omega)`. Establish `hZF : (CyclotomicLayer.zhatLayer r).1 ≤ F.1`.

Rewrite using `[hrq, CyclotomicLayer.zhatLayer_coe]`. Conclude with `(CyclotomicLayer.zhatLayerField_le_rootsOfUnityField ⟨ℓ, hℓ⟩ a).trans (rootsOfUnityField_pow_le (a := a + Cyclotomic.unitsLevel ℓ) (b := b) (by omega))`. Establish `hE'E : E' ≤ E`. Express the relevant statement in the definitionally equal form `(K.1 ⊔ F₂.1) ⊔ (CyclotomicLayer.zhatLayer r).1 ≤ K.1 ⊔ F.1`. Conclude with `sup_le (sup_le le_sup_left (hF₂F.trans le_sup_right)) (hZF.trans le_sup_right)`.

Establish `: Fact (E' ≤ E)` using `⟨hE'E⟩`. Establish `hKE : ∀ y ∈ E.1, y ∈ maxUnramifiedOutside K.1 ℚ̄ S` using `mem_maxUnramifiedOutside_of_mem_compositum (mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b)`. Establish `hres : (unitsResField K E 2).hom x = 0`. Establish `hKE' : Fact (K ≤ E')` using `⟨(Fact.out : K ≤ K').trans (Fact.out : K' ≤ E')⟩`. Establish `h1` using `unitsResField_comp_unitsResField (K := K) (E := E') (M := E) 2`.

Establish `h2` using `unitsResField_comp_unitsResField (K := K) (E := K') (M := E') 2`. Rewrite using `[← h1, ConcreteCategory.comp_apply, ← h2, ConcreteCategory.comp_apply]`. Express the relevant statement in the definitionally equal form `(unitsResField E' E 2).hom ((unitsResField K' E' 2).hom x') = 0`. Rewrite using `[hsplit, map_zero]`. Conclude with `exists_gsBrauerInfl_eq_of_unitsResField_eq_zero K S hKE x hres`.
-/
theorem exists_gsBrauerInfl_eq (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : cohomology (unitsLimitRep K) 2) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    ∃ y, (gsBrauerInfl K S 2).hom y = x := by
  classical
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩

  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let K' : FiniteSubfield := CyclotomicSymbol.compositum K F₂
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (F₂ ≤ K') := CyclotomicSymbol.fact_le_compositum_right K F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 K'.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ K')
  have : IsTotallyComplex K'.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) K'.1
  obtain ⟨ι'⟩ := nonempty_localEmbeddings K'
  set x' := (unitsResField K K' 2).hom x with hx'
  have hm : (ℓ ^ k) • x' = 0 := by rw [hx', ← map_nsmul, hx, map_zero]

  let T : Finset (HeightOneSpectrum (𝓞 K'.1)) :=
    (brauerLocal ι' x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨r, ⟨N, hr⟩, hdeg⟩ :=
    CyclotomicLayer.exists_pow_dvd_finrank_cyclotomicLayer K' T (pow_ne_zero k hℓ.ne_zero)
  let E' : FiniteSubfield := CyclotomicLayer.cyclotomicLayer K' r
  have hsplit : (unitsResField K' E' 2).hom x' = 0 := by
    refine unitsResField_eq_zero_of_dvd_finrank ι' x' (ℓ ^ k) hm (fun v => ?_) fun v hv w => ?_
    · have := subsingleton_cohomology_two_of_isComplex v (IsTotallyComplex.isComplex v)
      exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _
    · exact hdeg v (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact hv) w

  let a := k * (N + 1)
  let b := a + Cyclotomic.unitsLevel ℓ + 2
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ b), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum K F
  have hrq : r = Cyclotomic.primePowPNat ℓ a := by
    apply PNat.eq
    rw [hr, Cyclotomic.coe_primePowPNat, ← pow_mul]
  have hF₂F : F₂.1 ≤ F.1 := rootsOfUnityField_pow_le (by omega)
  have hZF : (CyclotomicLayer.zhatLayer r).1 ≤ F.1 := by
    rw [hrq, CyclotomicLayer.zhatLayer_coe]
    exact (CyclotomicLayer.zhatLayerField_le_rootsOfUnityField ⟨ℓ, hℓ⟩ a).trans
      (rootsOfUnityField_pow_le (a := a + Cyclotomic.unitsLevel ℓ) (b := b) (by omega))
  have hE'E : E' ≤ E := by
    change (K.1 ⊔ F₂.1) ⊔ (CyclotomicLayer.zhatLayer r).1 ≤ K.1 ⊔ F.1
    exact sup_le (sup_le le_sup_left (hF₂F.trans le_sup_right)) (hZF.trans le_sup_right)
  have : Fact (E' ≤ E) := ⟨hE'E⟩
  have hKE : ∀ y ∈ E.1, y ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_mem_compositum
      (mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b)
  have hres : (unitsResField K E 2).hom x = 0 := by
    have hKE' : Fact (K ≤ E') := ⟨(Fact.out : K ≤ K').trans (Fact.out : K' ≤ E')⟩
    have h1 := unitsResField_comp_unitsResField (K := K) (E := E') (M := E) 2
    have h2 := unitsResField_comp_unitsResField (K := K) (E := K') (M := E') 2
    rw [← h1, ConcreteCategory.comp_apply, ← h2, ConcreteCategory.comp_apply]
    change (unitsResField E' E 2).hom ((unitsResField K' E' 2).hom x') = 0
    rw [hsplit, map_zero]
  exact exists_gsBrauerInfl_eq_of_unitsResField_eq_zero K S hKE x hres

end

end GroundTheory.ProfCoh
