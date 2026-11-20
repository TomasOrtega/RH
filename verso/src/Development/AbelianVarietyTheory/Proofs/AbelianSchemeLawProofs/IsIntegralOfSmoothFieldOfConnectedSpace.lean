import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

/- English proof (translation)
Establish `hK : IsNormalScheme (Spec (.of K))` using `inferInstance`. Establish `: IsNormalScheme Z` using `(isNormalScheme_iff Z).mpr (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((isNormalScheme_iff _).mp hK))`. Establish `: IsLocallyNoetherian Z` using `LocallyOfFiniteType.isLocallyNoetherian g`. Conclude with `IsNormalScheme.isIntegral_of_connectedSpace Z`.
-/
theorem isIntegral_of_smooth_field_of_connectedSpace {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] [ConnectedSpace Z] : IsIntegral Z := by
  have hK : IsNormalScheme (Spec (.of K)) := inferInstance
  have : IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsNormalScheme.isIntegral_of_connectedSpace Z

/- English proof (translation)
Use `⟨fun K _ y Z fst snd h ↦ ?_⟩` and prove the remaining obligations. Establish `: Smooth snd` using `MorphismProperty.of_isPullback (P := @Smooth) h ‹_›`. Establish `: ConnectedSpace Z` using `GeometricallyConnected.geometrically_connectedSpace y fst snd h`. Conclude with `isIntegral_of_smooth_field_of_connectedSpace snd`.
-/
theorem geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field_of_connectedSpace snd

/- English proof (translation)
The claim follows from `geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom`.
-/
theorem grpObj_geometricallyIntegral_of_smooth (S : Scheme.{0}) (H : Over S) [GrpObj H]
    [Smooth H.hom] [GeometricallyConnected H.hom] : GeometricallyIntegral H.hom :=
  geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom

end GlobalTheory
