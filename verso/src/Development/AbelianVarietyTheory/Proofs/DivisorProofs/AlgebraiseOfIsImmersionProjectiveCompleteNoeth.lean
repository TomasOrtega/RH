import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersionStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

/- English proof (translation)
Introduce `R _ _ I hI W P j p hp hj`. Establish `hpb : IsProjBy p` using `(GlobalTheory.ProjSpace.isProjBy_iff_isProjOver p).2 hp`. Establish `hprop : IsProper p` using `GlobalTheory.AbLaw.isProper_of_isProjBy R P p hpb`. Establish `hA : Alg p I` using `GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective R I hI P p hpb`. Establish `hjac : I ≤ Ideal.jacobson ⊥` using `IsAdicComplete.le_jacobson_bot I`.

Establish `hsep : IsSeparated p` using `inferInstance`. Establish `hU : Alg (j.coborderRange.ι ≫ p) I` using `GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion R I hjac P _ p j.coborderRange.ι hsep inferInstance hA`. Establish `hsepU : IsSeparated (j.coborderRange.ι ≫ p)` using `inferInstance`. Establish `hW` using `GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion R I _ W (j.coborderRange.ι ≫ p) j.liftCoborder hsepU inferInstance hU`. Rewrite `hW` using `[← Category.assoc, Scheme.Hom.liftCoborder_ι]`. Then use the resulting hypothesis.
-/
theorem alg_of_isImmersion_isProjOver :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)),
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  intro R _ _ I hI W P j p hp hj
  have hpb : IsProjBy p := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver p).2 hp
  have hprop : IsProper p := GlobalTheory.AbLaw.isProper_of_isProjBy R P p hpb
  have hA : Alg p I := GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective R I hI P p hpb
  have hjac : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hsep : IsSeparated p := inferInstance
  have hU : Alg (j.coborderRange.ι ≫ p) I :=
    GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion R I hjac P _ p j.coborderRange.ι hsep inferInstance hA
  have hsepU : IsSeparated (j.coborderRange.ι ≫ p) := inferInstance
  have hW := GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion R I _ W (j.coborderRange.ι ≫ p) j.liftCoborder hsepU inferInstance hU
  rwa [← Category.assoc, Scheme.Hom.liftCoborder_ι] at hW

end GlobalTheory.FormalAlg
