import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes

open ReciprocityTheory.ChartRestriction.G.Semi

structure IsAbelianScheme {S : Scheme.{u}} (A : Over S) [GrpObj A] : Prop where
  smooth : Smooth A.hom
  proper : IsProper A.hom
  geometricallyConnected : GeometricallyConnected A.hom
  comm : IsCommMonObj A

structure IsShortExact {S : Scheme.{u}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) : Prop where
  isMonHom_i : IsMonHom i
  isMonHom_q : IsMonHom q
  isKernel : IsPullback i (toUnit T) q (η : 𝟙_ (Over S) ⟶ B)
  flat : Flat q.left
  surjective : Surjective q.left
  finitePresentation : LocallyOfFinitePresentation q.left

def IsTorusExtension {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Prop :=
  IsCommMonObj G ∧
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
      (B : Over (Spec (CommRingCat.of k))) (_ : GrpObj B)
      (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (q : G ⟶ B),
      IsAbelianScheme B ∧ IsShortExact i q

structure IsSemiAbelianScheme {S : Scheme.{u}} (G : Over S) [GrpObj G] : Prop where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  locallyOfFiniteType : LocallyOfFiniteType G.hom
  quasiCompact : QuasiCompact G.hom
  comm : IsCommMonObj G
  geometricFibre : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
    IsTorusExtension ((Over.pullback s).obj G)

/- English proof (translation)
The claim follows from `inferInstanceAs (Smooth (𝟙 S)) proper := inferInstanceAs (IsProper (𝟙 S)) geometricallyConnected := by change GeometricallyConnected (𝟙 S) refine ⟨fun K _ y Z fst snd h => ?_⟩ have : IsIso snd := h.isIso_snd_of_isIso exact (Scheme.homeoOfIso (asIso snd)).symm.surjective.connected …`.
-/
theorem isAbelianScheme_unit (S : Scheme.{u}) : IsAbelianScheme (𝟙_ (Over S)) where
  smooth := inferInstanceAs (Smooth (𝟙 S))
  proper := inferInstanceAs (IsProper (𝟙 S))
  geometricallyConnected := by
    change GeometricallyConnected (𝟙 S)
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    have : IsIso snd := h.isIso_snd_of_isIso
    exact (Scheme.homeoOfIso (asIso snd)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso snd)).symm.continuous
  comm := inferInstance

section SplitTorus

variable (X : Type u) [AddCommGroup X]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Express the relevant statement in the definitionally equal form `(algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).Flat`. Rewrite using `[RingHom.flat_algebraMap_iff]`. Establish `: Module.Free (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)` using `inferInstance`.

Use `infer_instance`.
-/
theorem flat_splitTorusAff : Flat (splitTorusAff ZU X).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).Flat
  rw [RingHom.flat_algebraMap_iff]
  have : Module.Free (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X) := inferInstance
  infer_instance

/- English proof (translation)
Express the relevant statement in the definitionally equal form `LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]`. Express the relevant statement in the definitionally equal form `(algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).FinitePresentation`. Rewrite using `[RingHom.finitePresentation_algebraMap]`. Establish `: IsNoetherianRing (ULift.{u} ℤ)` using `isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm`.

Establish `: AddGroup.FG X` using `Module.Finite.iff_addGroup_fg.1 inferInstance`. Establish `: AddMonoid.FG X` using `AddGroup.fg_iff_addMonoid_fg.1 inferInstance`. Conclude with `Algebra.FinitePresentation.of_finiteType.1 inferInstance`.
-/
theorem finitePresentation_splitTorusAff [Module.Finite ℤ X] :
    LocallyOfFinitePresentation (splitTorusAff ZU X).hom := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ZU (torusRing ZU X))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) X)).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 inferInstance
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance

/- English proof (translation)
Establish `hc : IsCommMonObj (splitTorus (Spec (CommRingCat.of k)) X)`. Unfold `splitTorus`. Use `infer_instance`. Establish `h1` using `flat_splitTorusAff X`. Establish `h2` using `finitePresentation_splitTorusAff X`.

Establish `e : (toUnit (splitTorus (Spec (CommRingCat.of k)) X)).left = (splitTorus (Spec (CommRingCat.of k)) X).hom`. Simplify using `using Over.w (toUnit (splitTorus (Spec (CommRingCat.of k)) X))`. Use `⟨hc, X, inferInstance, inferInstance, inferInstance, 𝟙_ _, inferInstance, 𝟙 _, toUnit _, isAbelianScheme_unit _, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: IsIso (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _)`. Rewrite using `[toUnit_unique (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _) (𝟙 _)]`.

Use `infer_instance`. Conclude with `IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩`. Rewrite using `[e]`. Conclude with `inferInstanceAs (Flat (pullback.snd _ _))`. Rewrite using `[e]`.

Conclude with `⟨fun y => ⟨(η : 𝟙_ _ ⟶ splitTorus (Spec (CommRingCat.of k)) X).left y, by`. Rewrite using `[← Scheme.Hom.comp_apply, Over.w]`. Use the proof step `rfl⟩⟩`. Rewrite using `[e]`. Conclude with `inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))`.
-/
theorem isTorusExtension_splitTorus (k : Type u) [Field k] [Module.Free ℤ X] [Module.Finite ℤ X] :
    IsTorusExtension (splitTorus (Spec (CommRingCat.of k)) X) := by
  have hc : IsCommMonObj (splitTorus (Spec (CommRingCat.of k)) X) := by
    unfold splitTorus; infer_instance
  have h1 := flat_splitTorusAff X
  have h2 := finitePresentation_splitTorusAff X
  have e : (toUnit (splitTorus (Spec (CommRingCat.of k)) X)).left =
      (splitTorus (Spec (CommRingCat.of k)) X).hom := by
    simpa using Over.w (toUnit (splitTorus (Spec (CommRingCat.of k)) X))
  refine ⟨hc, X, inferInstance, inferInstance, inferInstance, 𝟙_ _, inferInstance, 𝟙 _,
    toUnit _, isAbelianScheme_unit _, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · have : IsIso (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _) := by
      rw [toUnit_unique (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _) (𝟙 _)]
      infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  · rw [e]; exact inferInstanceAs (Flat (pullback.snd _ _))
  · rw [e]
    exact ⟨fun y => ⟨(η : 𝟙_ _ ⟶ splitTorus (Spec (CommRingCat.of k)) X).left y, by
      rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  · rw [e]; exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

end SplitTorus

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
