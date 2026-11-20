import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittedTiesBoundEventual
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigTop.Fun.gBig_atTied` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFittedTiesBoundEventual.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.fitted_ties_bound_eventual : ∀ Q : GlobalTheory.SqTop.GP, SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → Lf (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  first | exact @GlobalTheory.BigTop.Fun.gBig_atTied | exact GlobalTheory.BigTop.Fun.gBig_atTied | (intros; apply GlobalTheory.BigTop.Fun.gBig_atTied <;> assumption)
