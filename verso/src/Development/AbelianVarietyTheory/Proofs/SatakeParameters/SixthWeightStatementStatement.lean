import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSixthWeightStatement.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.sixth_weight_statement : PurityStringWeight := by
  first | exact @GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | exact GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | (intros; apply GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity <;> assumption)
