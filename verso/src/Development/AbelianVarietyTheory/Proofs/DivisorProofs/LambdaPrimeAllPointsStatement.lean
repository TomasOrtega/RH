import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftWeightForced.atPts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLambdaPrimeAllPoints.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.lambda_prime_all_points : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ, Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i) (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  first | exact @GlobalTheory.LiftWeightForced.atPts | exact GlobalTheory.LiftWeightForced.atPts | (intros; apply GlobalTheory.LiftWeightForced.atPts <;> assumption)
