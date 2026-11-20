import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEquality
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSixthCharacterEquality.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.sixth_character_equality : HeckeCharEqOfLAdicRealisation := by
  first | exact @GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds | exact GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds | (intros; apply GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds <;> assumption)
