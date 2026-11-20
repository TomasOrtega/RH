import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEqualityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthCharacterEqualityHoldsAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FSixthCharacterEqualityHoldsAltAlt.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  first | exact @_root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | exact _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | (intros; apply _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt <;> assumption)
end
