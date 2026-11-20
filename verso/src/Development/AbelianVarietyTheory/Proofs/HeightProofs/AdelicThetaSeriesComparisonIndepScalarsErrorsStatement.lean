import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicThetaSeriesComparisonIndepScalarsErrors
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PlugPt.Side.exportTie_upd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FAdelicThetaSeriesComparisonIndepScalarsErrors.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.adelicThetaSeriesComparison_indep_scalars_errors : ∀ (D : D7) (nch : NChoice D) (s : Side D nch) kap lam err, Nonempty (GlobalTheory.SeriesTie.ExportTie s.YS s.v₀) → Nonempty (GlobalTheory.SeriesTie.ExportTie (s.upd kap lam err).YS (s.upd kap lam err).v₀) := by
  first | exact @GlobalTheory.PlugPt.Side.exportTie_upd | exact GlobalTheory.PlugPt.Side.exportTie_upd | (intros; apply GlobalTheory.PlugPt.Side.exportTie_upd <;> assumption)
