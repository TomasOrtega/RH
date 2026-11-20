import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.thb_tie` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaBoundFittedIdentity.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.theta_bound_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → ThbSt → Thb @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.thb_tie | exact GlobalTheory.BigTop.Fun.thb_tie | (intros; apply GlobalTheory.BigTop.Fun.thb_tie <;> assumption)
