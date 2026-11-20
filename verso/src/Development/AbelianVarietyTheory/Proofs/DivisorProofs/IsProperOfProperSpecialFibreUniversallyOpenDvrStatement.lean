import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvr
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibreProperDvr.isProper_of_specialFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsProperOfProperSpecialFibreUniversallyOpenDvr.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → UniversallyOpen f → GeometricallyIrreducible f → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProperDvr.isProper_of_specialFibre | exact GlobalTheory.FibreProperDvr.isProper_of_specialFibre | (intros; apply GlobalTheory.FibreProperDvr.isProper_of_specialFibre <;> assumption)
