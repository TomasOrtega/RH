import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.StratumOpenCover

/- English proof (translation)
Establish `hB : IsField B` using `MulEquiv.isField (Field.toIsField L) e.symm.toMulEquiv`. Set `: Field B` to `hB.toField`. Establish `: Algebra.IsAlgebraic A B` using `e.isAlgebraic`. Establish `: IsFractionRing (integralClosure A B) B` using `integralClosure.isFractionRing_of_algebraic (A := A) (L := B) fun x hx => by`. Apply `hinj` to reduce the goal to its premises.

Apply `e.injective` to reduce the goal to its premises. Simplify using `using hx`. Conclude with `IsPreimmersion.of_isLocalization (R := integralClosure A B) (S := B) (nonZeroDivisors _)`.
-/
theorem isPreimmersion_val (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    (L : Type) [Field L] [Algebra A L] [Algebra.IsAlgebraic A L]
    (hinj : Function.Injective (algebraMap A L)) (e : L ≃ₐ[A] B) :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom)) := by
  have hB : IsField B := MulEquiv.isField (Field.toIsField L) e.symm.toMulEquiv
  let : Field B := hB.toField
  have : Algebra.IsAlgebraic A B := e.isAlgebraic
  have : IsFractionRing (integralClosure A B) B :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := B) fun x hx => by
      apply hinj
      apply e.injective
      simpa using hx
  exact IsPreimmersion.of_isLocalization (R := integralClosure A B) (S := B) (nonZeroDivisors _)

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ`. Use `set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) with hf`. Establish `htop : f ⁻¹ᵁ U = ⊤`. Use `top_le_iff.mp fun x _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f x ∈ U`.

Rewrite using `[hf, Scheme.Hom.comp_apply]`. Establish `: Z.fromSpecStalk (genericPoint Z) (Spec.map φ x) ∈ Set.range (Z.fromSpecStalk (genericPoint Z))` using `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Conclude with `this.mem_open U.isOpen hxU`. Set `` to `(f.app U).hom.toAlgebra`.

Set `ψ : CommRingCat.of L ⟶ Γ(Spec (.of L), f ⁻¹ᵁ U)` to `(Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).presheaf.map (homOfLE le_top).op`. Establish `: IsIso (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤))` using `⟨homOfLE htop.ge, rfl, rfl⟩`. Establish `hψ : IsIso ψ` using `inferInstance`. Establish `happ : f.app U = Z.presheaf.germ U _ hxU ≫ φ ≫ ψ`. Simplify using `only [f, ψ, Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hxU, Category.assoc]`.

Rewrite using `[Scheme.Hom.naturality, Scheme.ΓSpecIso_inv_naturality_assoc φ]`. Both sides reduce to the same expression. Establish `: Nonempty U` using `⟨⟨_, hxU⟩⟩`. Set `: Algebra Z.functionField L` to `φ.hom.toAlgebra`. Set `: Algebra Γ(Z, U) L` to `(Z.presheaf.germ U _ hxU ≫ φ).hom.toAlgebra`.

Establish `: IsScalarTower Γ(Z, U) Z.functionField L` using `.of_algebraMap_eq fun _ => rfl`. Establish `: IsFractionRing Γ(Z, U) Z.functionField` using `functionField_isFractionRing_of_isAffineOpen Z U hU`. Establish `: Module.Finite Z.functionField L` using `hφ`. Establish `: Algebra.IsAlgebraic Γ(Z, U) L` using `(IsFractionRing.comap_isAlgebraic_iff (K := Z.functionField)).mpr inferInstance`. Establish `hinj : Function.Injective (algebraMap Γ(Z, U) L)`.

Rewrite using `[IsScalarTower.algebraMap_eq Γ(Z, U) Z.functionField L]`. Conclude with `(algebraMap Z.functionField L).injective.comp (IsFractionRing.injective _ _)`. Set `e : L ≃ₐ[Γ(Z, U)] Γ(Spec (.of L), f ⁻¹ᵁ U)` to `{ (asIso ψ).commRingCatIsoToRingEquiv with commutes' := fun a => by`. Express the relevant statement in the definitionally equal form `((Z.presheaf.germ U _ hxU ≫ φ) ≫ ψ).hom a = (f.app U).hom a`. Rewrite using `[happ, Category.assoc] }`.

Establish `h1` using `isPreimmersion_val Γ(Z, U) Γ(Spec (.of L), f ⁻¹ᵁ U) L hinj e`. Establish `h2` using `f.ι_toNormalization ⟨U, hU⟩`. Establish `hW : IsAffineOpen (f ⁻¹ᵁ U)` using `htop ▸ isAffineOpen_top _`. Establish `h3 : IsIso (f ⁻¹ᵁ U).toSpecΓ`. Rewrite using `[← hW.isoSpec_hom]`.

Use `infer_instance`. Establish `h4 : IsIso (f ⁻¹ᵁ U).ι`. Rewrite using `[htop]`. Conclude with `inferInstanceAs (IsIso (Spec (.of L)).topIso.hom)`. Establish `h5 : IsPreimmersion ((f ⁻¹ᵁ U).ι ≫ f.toNormalization)`.

Rewrite using `[h2]`. Establish `h7 : IsOpenImmersion (f.normalizationOpenCover.f ⟨U, hU⟩)` using `f.normalizationOpenCover.map_prop _`. Establish `h8 : IsPreimmersion (f.normalizationOpenCover.f ⟨U, hU⟩)` using `(fun {X Y : Scheme.{0}} (g : X ⟶ Y) (_ : IsOpenImmersion g) => (inferInstance : IsPreimmersion g)) _ h7`. Conclude with `@IsPreimmersion.comp _ _ _ _ _ inferInstance (@IsPreimmersion.comp _ _ _ _ _ h1 h8)`. Establish `h6 : IsPreimmersion (inv (f ⁻¹ᵁ U).ι ≫ (f ⁻¹ᵁ U).ι ≫ f.toNormalization)` using `inferInstance`.

Rewrite `h6` using `[IsIso.inv_hom_id_assoc]`. Then use the resulting hypothesis.
-/
theorem isPreimmersion_toNormalization (Z : Scheme.{0}) [IsIntegral Z] {L : Type} [Field L]
    (φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L) (hφ : φ.hom.Finite) :
    IsPreimmersion (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).toNormalization := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Z)) isOpen_univ
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) with hf
  have htop : f ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    change f x ∈ U
    rw [hf, Scheme.Hom.comp_apply]
    have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ x) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hxU
  let := (f.app U).hom.toAlgebra
  let ψ : CommRingCat.of L ⟶ Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).presheaf.map (homOfLE le_top).op
  have : IsIso (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)) := ⟨homOfLE htop.ge, rfl, rfl⟩
  have hψ : IsIso ψ := inferInstance
  have happ : f.app U = Z.presheaf.germ U _ hxU ≫ φ ≫ ψ := by
    simp only [f, ψ, Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hxU, Category.assoc]
    rw [Scheme.Hom.naturality, Scheme.ΓSpecIso_inv_naturality_assoc φ]
    rfl
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let : Algebra Z.functionField L := φ.hom.toAlgebra
  let : Algebra Γ(Z, U) L := (Z.presheaf.germ U _ hxU ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Z.functionField L := .of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Z, U) Z.functionField := functionField_isFractionRing_of_isAffineOpen Z U hU
  have : Module.Finite Z.functionField L := hφ
  have : Algebra.IsAlgebraic Γ(Z, U) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := Z.functionField)).mpr inferInstance
  have hinj : Function.Injective (algebraMap Γ(Z, U) L) := by
    rw [IsScalarTower.algebraMap_eq Γ(Z, U) Z.functionField L]
    exact (algebraMap Z.functionField L).injective.comp (IsFractionRing.injective _ _)
  let e : L ≃ₐ[Γ(Z, U)] Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    { (asIso ψ).commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        change ((Z.presheaf.germ U _ hxU ≫ φ) ≫ ψ).hom a = (f.app U).hom a
        rw [happ, Category.assoc] }
  have h1 := isPreimmersion_val Γ(Z, U) Γ(Spec (.of L), f ⁻¹ᵁ U) L hinj e
  have h2 := f.ι_toNormalization ⟨U, hU⟩
  have hW : IsAffineOpen (f ⁻¹ᵁ U) := htop ▸ isAffineOpen_top _
  have h3 : IsIso (f ⁻¹ᵁ U).toSpecΓ := by
    rw [← hW.isoSpec_hom]; infer_instance
  have h4 : IsIso (f ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Spec (.of L)).topIso.hom)
  have h5 : IsPreimmersion ((f ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [h2]
    have h7 : IsOpenImmersion (f.normalizationOpenCover.f ⟨U, hU⟩) := f.normalizationOpenCover.map_prop _
    have h8 : IsPreimmersion (f.normalizationOpenCover.f ⟨U, hU⟩) :=
      (fun {X Y : Scheme.{0}} (g : X ⟶ Y) (_ : IsOpenImmersion g) => (inferInstance : IsPreimmersion g)) _ h7
    exact @IsPreimmersion.comp _ _ _ _ _ inferInstance (@IsPreimmersion.comp _ _ _ _ _ h1 h8)
  have h6 : IsPreimmersion (inv (f ⁻¹ᵁ U).ι ≫ (f ⁻¹ᵁ U).ι ≫ f.toNormalization) := inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h6

end PositivityTheory.Xgn.StratumOpenCover

/- English proof (translation)
Introduce `Z _ s _ _ L _ z hz L' _ _ _`. Take `⟨e, rfl⟩` from `hz`. Take `⟨χ, hχ⟩` from `Spec.map_surjective e.hom`. Establish `: IsIso (Spec.map χ)` using `hχ ▸ inferInstance`. Establish `hχ' : IsIso χ` using `(isIso_SpecMap_iff).mp this |> (ConcreteCategory.isIso_iff_bijective χ).mpr`.

Set `φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L'` to `χ ≫ CommRingCat.ofHom (algebraMap L L')`. Establish `hφ : φ.hom.Finite` using `RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance) (.of_surjective _ (ConcreteCategory.bijective_of_isIso χ).2)`. Establish `hf : spMap (algebraMap L L') ≫ e.hom ≫ Z.fromSpecStalk (genericPoint Z) = Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)`. Rewrite using `[← hχ, Spec.map_comp, Category.assoc]`. Rewrite using `[hf]`.

Establish `: CharZero L'`. Take `⟨ρ, -⟩` from `Spec.map_surjective (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) ≫ s)`. Conclude with `charZero_of_injective_ringHom (R := ℚ) ρ.hom.injective`. Establish `hfin` using `GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s (genericPoint Z) φ hφ.finiteType.essFiniteType`. Establish `hpre` using `PositivityTheory.Xgn.StratumOpenCover.isPreimmersion_toNormalization Z φ hφ`.

Establish `hdom : IsDominant (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z))`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hx : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint L') = genericPoint Z`. Establish `: Z.fromSpecStalk (genericPoint Z) (Spec.map φ (IsLocalRing.closedPoint L')) ∈ Set.range (Z.fromSpecStalk (genericPoint Z))` using `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`.

Conclude with `(Specializes.antisymm this (genericPoint_specializes _)).eq`. Use `Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hx⟩) ?_` and prove the remaining obligations. Conclude with `dense_iff_closure_eq.mpr (genericPoint_spec Z)`. Use `set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)`. Establish `: IsDominant (f.toNormalization ≫ f.fromNormalization)`.

Rewrite using `[Scheme.Hom.toNormalization_fromNormalization]`. Conclude with `hdom`. Establish `: IsDominant f.fromNormalization` using `.of_comp f.toNormalization _`. Use `⟨f.normalization, inferInstance, f.fromNormalization, f.toNormalization, hfin, inferInstance, GlobalTheory.IsNormalScheme.pred _, GlobalTheory.IsGenericPointHom.of_isPreimmersion _, Scheme.Hom.toNormalization_fromNormalization _⟩` and prove the remaining obligations.
-/
theorem PositivityTheory.Xgn.stratum_finite_normal_cover : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  intro Z _ s _ _ L _ z hz L' _ _ _
  obtain ⟨e, rfl⟩ := hz
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.hom
  have : IsIso (Spec.map χ) := hχ ▸ inferInstance
  have hχ' : IsIso χ := (isIso_SpecMap_iff).mp this |> (ConcreteCategory.isIso_iff_bijective χ).mpr
  let φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L' := χ ≫ CommRingCat.ofHom (algebraMap L L')
  have hφ : φ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso χ).2)
  have hf : spMap (algebraMap L L') ≫ e.hom ≫ Z.fromSpecStalk (genericPoint Z) =
      Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) := by
    rw [← hχ, Spec.map_comp, Category.assoc]
  rw [hf]
  have : CharZero L' := by
    obtain ⟨ρ, -⟩ := Spec.map_surjective (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) ≫ s)
    exact charZero_of_injective_ringHom (R := ℚ) ρ.hom.injective
  have hfin := GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s (genericPoint Z) φ
    hφ.finiteType.essFiniteType
  have hpre := PositivityTheory.Xgn.StratumOpenCover.isPreimmersion_toNormalization Z φ hφ
  have hdom : IsDominant (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) := by
    refine ⟨?_⟩
    have hx : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint L') =
        genericPoint Z := by
      have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ (IsLocalRing.closedPoint L')) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecStalk] at this
      exact (Specializes.antisymm this (genericPoint_specializes _)).eq
    refine Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hx⟩) ?_
    exact dense_iff_closure_eq.mpr (genericPoint_spec Z)
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact hdom
  have : IsDominant f.fromNormalization := .of_comp f.toNormalization _
  refine ⟨f.normalization, inferInstance, f.fromNormalization, f.toNormalization, hfin,
    inferInstance, GlobalTheory.IsNormalScheme.pred _, GlobalTheory.IsGenericPointHom.of_isPreimmersion _,
    Scheme.Hom.toNormalization_fromNormalization _⟩
