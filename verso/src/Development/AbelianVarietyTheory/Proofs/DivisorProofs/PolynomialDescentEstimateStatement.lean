import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.desPol` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialDescentEstimate.lean&line=180#L180)
-/
theorem _root_.GlobalTheory.T.polynomial_descent_estimate : DesPol := by
  first | exact @GlobalTheory.BigTop.Fun.desPol | exact GlobalTheory.BigTop.Fun.desPol | (intros; apply GlobalTheory.BigTop.Fun.desPol <;> assumption)
