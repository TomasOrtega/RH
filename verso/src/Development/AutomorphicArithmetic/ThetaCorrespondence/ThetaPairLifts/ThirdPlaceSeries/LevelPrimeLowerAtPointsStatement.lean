import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembersStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelPrimeLowerAtPoints
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FLevelPrimeLowerAtPoints.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.trace_lower_bound_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∀ u : D.what₂.Word, O.L.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr D u) := by
  first | exact @_root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt | exact _root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt | (intros; apply _root_.GlobalTheory.Core.LevLow.levelPrime_lower_at_points_alt <;> assumption)
end
