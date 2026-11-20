import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPoint
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Plug.tied_cfOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FCoreFrameCompatibleConstructedPoint.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.coreFrameCompatible_constructed_point : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  first | exact @GlobalTheory.Plug.tied_cfOf | exact GlobalTheory.Plug.tied_cfOf | (intros; apply GlobalTheory.Plug.tied_cfOf <;> assumption)
