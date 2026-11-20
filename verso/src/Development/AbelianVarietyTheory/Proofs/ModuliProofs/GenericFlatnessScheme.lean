import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericFlatScheme

/- English proof (translation)
Take `⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s` from `⟨Spec.preimage s, Spec.map_preimage s⟩`. Establish `hg : g.hom.FiniteType` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance`. Set `: Algebra R A` to `g.hom.toAlgebra`. Establish `: Algebra.FiniteType R A` using `hg`. Take `⟨a, ha, hfree⟩` from `(GlobalTheory.generic_freeness R).2.1 A A`.

Use `⟨a, ha, fun R' _ φ hφ => ?_⟩` and prove the remaining obligations. Set `: Algebra R R'` to `φ.toAlgebra`. Set `: Algebra (Localization.Away a) R'` to `(IsLocalization.Away.lift a hφ).toAlgebra`. Establish `: IsScalarTower R (Localization.Away a) R'` using `IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm`. Use `hfree` as an intermediate fact.

Establish `hbc : IsBaseChange (Localization.Away a) (LocalizedModule.mkLinearMap (Submonoid.powers a) A)` using `(isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp inferInstance`. Establish `: Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A)` using `Module.Free.of_equiv hbc.equiv.symm`. Establish `hflat : Module.Flat R' (R' ⊗[R] A)` using `Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm`. Establish `hA : g = CommRingCat.ofHom (algebraMap R A)` using `rfl`. Establish `hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A))))` using `(HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)`.

Rewrite using `[hA]`. Express the relevant statement in the definitionally equal form `Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))`. Rewrite using `[← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]`. Use `infer_instance`.
-/
theorem affine (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : CommRingCat.{0})
    (s : Spec A ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd s (spMap φ)) := by
  obtain ⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  have hg : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra R A := g.hom.toAlgebra
  have : Algebra.FiniteType R A := hg
  obtain ⟨a, ha, hfree⟩ := (GlobalTheory.generic_freeness R).2.1 A A
  refine ⟨a, ha, fun R' _ φ hφ => ?_⟩
  let : Algebra R R' := φ.toAlgebra

  let : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a hφ).toAlgebra
  have : IsScalarTower R (Localization.Away a) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm
  have := hfree
  have hbc : IsBaseChange (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) A) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      inferInstance
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A) :=
    Module.Free.of_equiv hbc.equiv.symm
  have hflat : Module.Flat R' (R' ⊗[R] A) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm

  have hA : g = CommRingCat.ofHom (algebraMap R A) := rfl
  have hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  rw [hA]
  change Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]
  infer_instance

end GenericFlatScheme

/- English proof (translation)
Introduce `R _ _ _ Z s hs hq`. Use `hs` as an intermediate fact. Use `hq` as an intermediate fact. Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace s`. Set `𝒰` to `Z.affineCover.finiteSubcover`.

Establish `key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ))` using `fun i => by`. Establish `: LocallyOfFiniteType (𝒰.f i ≫ s)` using `MorphismProperty.comp_mem _ _ _ (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs`. Conclude with `@GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this`. Use `choose e he0 heF using key`. Use `⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩` and prove the remaining obligations.

Establish `hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat` using `HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)`. Use `(IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat) (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))`. Use `heF i R' φ (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)` as an intermediate fact. Apply the tactic sequence `have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) = ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫ pullback.snd (𝒰.f i ≫ s) (spMap φ) := by`.

Rewrite using `[Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]`. Rewrite using `[h]`. Use `infer_instance`.
-/
theorem generic_flatness_scheme :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R),
      LocallyOfFiniteType s → QuasiCompact s → ∃ f : R, f ≠ 0 ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
          Flat (pullback.snd s (spMap φ)) := by
  intro R _ _ _ Z s hs hq
  have := hs
  have := hq
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := Z.affineCover.finiteSubcover
  have key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ)) :=
    fun i => by
      have : LocallyOfFiniteType (𝒰.f i ≫ s) := MorphismProperty.comp_mem _ _ _
        (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs
      exact @GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this
  choose e he0 heF using key
  refine ⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩

  have hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_
  change Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))
  have := heF i R' φ
    (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)
  have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) =
      ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫
        pullback.snd (𝒰.f i ≫ s) (spMap φ) := by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  rw [h]
  infer_instance

end GlobalTheory
