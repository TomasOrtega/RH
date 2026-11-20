import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h A K L _ _ _ _ _ _ _ _ _ _ _ => h A K L, fun h A _ _ _ K _ _ _ L _ _ _ _ _ => h A K L⟩`.
-/
theorem FiniteIntegralClosure.alg_iff :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
      (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
      Module.Finite A (integralClosure A L)) ↔
    (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
      [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
      [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :=
  ⟨fun h A K L _ _ _ _ _ _ _ _ _ _ _ => h A K L, fun h A _ _ _ K _ _ _ L _ _ _ _ _ => h A K L⟩

/- English proof (translation)
Use `hX.1` as an intermediate fact. Establish `h1` using `(toSpecZ X).finiteType_appLE (isAffineOpen_top (Spec (.of ℤ))) hU le_top`. Establish `h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2`. Establish `h3` using `h1.comp h2`. Rewrite `h3` using `[show ((toSpecZ X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom = algebraMap ℤ Γ(X, U) from RingHom.ext_int _ _]`.

Conclude with `RingHom.finiteType_algebraMap.mp h3`.
-/
theorem finiteType_sections_of_isFiniteTypeOverZ {X : Scheme.{0}} (hX : IsFiniteTypeOverZ X)
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have := hX.1
  have h1 := (toSpecZ X).finiteType_appLE (isAffineOpen_top (Spec (.of ℤ))) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2
  have h3 := h1.comp h2
  rw [show ((toSpecZ X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
    algebraMap ℤ Γ(X, U) from RingHom.ext_int _ _] at h3
  exact RingHom.finiteType_algebraMap.mp h3

/- English proof (translation)
Introduce `X _ hX L _ _ _ U hUa hU`. Use `hU` as an intermediate fact. Use `finiteType_sections_of_isFiniteTypeOverZ hX hUa` as an intermediate fact. Use `functionField_isFractionRing_of_isAffineOpen X U hUa` as an intermediate fact. Set `: Algebra Γ(X, U) L` to `((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra`.

Establish `: IsScalarTower Γ(X, U) X.functionField L` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `h Γ(X, U) X.functionField L`.
-/
theorem FiniteIntegralClosure.scheme_of_alg
    (h : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K]
      [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
      [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L)) :
    ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  intro X _ hX L _ _ _ U hUa hU
  have := hU
  have := finiteType_sections_of_isFiniteTypeOverZ hX hUa
  have := functionField_isFractionRing_of_isAffineOpen X U hUa
  let : Algebra Γ(X, U) L :=
    ((algebraMap X.functionField L).comp (algebraMap Γ(X, U) X.functionField)).toAlgebra
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h Γ(X, U) X.functionField L

/- English proof (translation)
Establish `h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L))) (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField` using `Spec_closedPoint`. Conclude with `(Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L))) (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans (h ▸ Scheme.fromSpecStalk_closedPoint)`.
-/
theorem genericSpecMap_closedPoint (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
      (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField :=
    Spec_closedPoint
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
    (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans
    (h ▸ Scheme.fromSpecStalk_closedPoint)

/- English proof (translation)
Establish `h` using `Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom (algebraMap Z.functionField L)) U hmem`. Conclude with `(Scheme.germ_stalkClosedPointTo _ U hmem).symm.trans h`.
-/
theorem genericSpecMap_app_iso (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] (U : Z.Opens) (hη : genericPoint Z ∈ U)
    (hmem : _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) ∈ U) :
    (_root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L).app U ≫
      ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      Z.presheaf.germ U (genericPoint Z) hη ≫ CommRingCat.ofHom (algebraMap Z.functionField L) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField L)) U hmem
  exact (Scheme.germ_stalkClosedPointTo _ U hmem).symm.trans h

/- English proof (translation)
Introduce `Z _ f _ _ L _ _ _`. Establish `e : f = toSpecZ Z` using `specZ_hom_ext _ _`. Establish `hX : IsFiniteTypeOverZ Z` using `⟨e ▸ ‹LocallyOfFiniteType f›, e ▸ ‹QuasiCompact f›⟩`. Use `set g := _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L with hg`. Use `{ finite_app := fun U hU => ?_ }` and prove the remaining obligations.

Set `` to `(g.app U).hom.toAlgebra`. Rewrite using `[g.fromNormalization_app hU, CommRingCat.hom_comp]`. Use `RingHom.Finite.comp ?_ ?_` and prove the remaining obligations. Conclude with `RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2`. Use `RingHom.finite_algebraMap.2 ?_` and prove the remaining obligations.

Break down `isEmpty_or_nonempty U with hU0 | hU0` into its components or cases. Establish `hb : U = ⊥` using `SetLike.coe_injective (by simpa using Set.isEmpty_coe_sort.mp hU0)`. Substitute `hb` using the available equality. Establish `: Subsingleton (integralClosure Γ(Z, ⊥) Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ ⊥))` using `Module.subsingleton Γ(Z, ⊥) _`. Conclude with `⟨⟨∅, Subsingleton.elim _ _⟩⟩`.

Establish `hη : genericPoint Z ∈ U` using `((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU0)`. Establish `hmem : g (IsLocalRing.closedPoint L) ∈ U`. Rewrite using `[hg, genericSpecMap_closedPoint]`. Conclude with `hη`. Establish `key` using `genericSpecMap_app_iso Z L U hη hmem`.

Set `: Algebra Γ(Z, U) L` to `((algebraMap Z.functionField L).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra`. Set `eR` to `((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv`. Set `eA : Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L` to `AlgEquiv.ofRingEquiv (f := eR) fun x => congrArg (fun φ => φ.hom x) key`. Establish `hfin` using `h Z hX L U hU hU0`. Conclude with `Module.Finite.equiv eA.mapIntegralClosure.symm.toLinearEquiv`.
-/
theorem FiniteIntegralClosure.normalization_of_scheme
    (h : ∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
      ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
        (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
        let : Algebra Γ(X, U) L :=
          ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
            haveI := hU; infer_instance))).toAlgebra
        Module.Finite Γ(X, U) (integralClosure Γ(X, U) L)) :
    _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement := by
  intro Z _ f _ _ L _ _ _
  have e : f = toSpecZ Z := specZ_hom_ext _ _
  have hX : IsFiniteTypeOverZ Z := ⟨e ▸ ‹LocallyOfFiniteType f›, e ▸ ‹QuasiCompact f›⟩
  set g := _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L with hg
  refine { finite_app := fun U hU => ?_ }
  let := (g.app U).hom.toAlgebra
  rw [g.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (g.normalizationObjIso hU).inv).2
  refine RingHom.finite_algebraMap.2 ?_
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · have hb : U = ⊥ := SetLike.coe_injective (by simpa using Set.isEmpty_coe_sort.mp hU0)
    subst hb
    have : Subsingleton (integralClosure Γ(Z, ⊥) Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ ⊥)) :=
      Module.subsingleton Γ(Z, ⊥) _
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have hη : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU0)
  have hmem : g (IsLocalRing.closedPoint L) ∈ U := by
    rw [hg, genericSpecMap_closedPoint]; exact hη
  have key := genericSpecMap_app_iso Z L U hη hmem
  let : Algebra Γ(Z, U) L :=
    ((algebraMap Z.functionField L).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
  let eR := ((Spec (CommRingCat.of L)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of L), g ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] L :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => congrArg (fun φ => φ.hom x) key
  have hfin := h Z hX L U hU hU0
  exact Module.Finite.equiv eA.mapIntegralClosure.symm.toLinearEquiv

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, -⟩`. Establish `hb` using `FiniteIntegralClosure.alg_iff.mp ha`. Conclude with `⟨hb, FiniteIntegralClosure.scheme_of_alg hb⟩`. Introduce and unpack `⟨hb, hs⟩`.

Conclude with `⟨FiniteIntegralClosure.alg_iff.mpr hb, FiniteIntegralClosure.normalization_of_scheme hs⟩`.
-/
theorem FiniteIntegralClosure.equiv :
    (_root_.GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.Statement ∧
      _root_.GroundTheory.Heights₂.Heights.Model.FiniteNormalization.Statement) ↔
    FiniteIntegralClosure.Statement := by
  constructor
  · rintro ⟨ha, -⟩
    have hb := FiniteIntegralClosure.alg_iff.mp ha
    exact ⟨hb, FiniteIntegralClosure.scheme_of_alg hb⟩
  · rintro ⟨hb, hs⟩
    exact ⟨FiniteIntegralClosure.alg_iff.mpr hb, FiniteIntegralClosure.normalization_of_scheme hs⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
