import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingleton
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SixthNumerics.numerics_and_rest` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FStringRankOneLengthAndMultisetSumSingleton.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton : Numerics ∧ Rest := by
  first | exact @GlobalTheory.SixthNumerics.numerics_and_rest | exact GlobalTheory.SixthNumerics.numerics_and_rest | (intros; apply GlobalTheory.SixthNumerics.numerics_and_rest <;> assumption)
