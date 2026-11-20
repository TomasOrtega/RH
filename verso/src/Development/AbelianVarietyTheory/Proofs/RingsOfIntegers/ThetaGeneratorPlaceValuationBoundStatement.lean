import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBound
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaBound.thBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FRingsOfIntegers%2FThetaGeneratorPlaceValuationBound.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.thetaGenerator_place_valuation_bound : ThBoundSt := by
  first | exact @GlobalTheory.ThetaBound.thBound | exact GlobalTheory.ThetaBound.thBound | (intros; apply GlobalTheory.ThetaBound.thBound <;> assumption)
