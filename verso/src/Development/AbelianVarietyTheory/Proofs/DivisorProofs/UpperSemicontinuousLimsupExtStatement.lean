import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperSemicontinuousLimsupExt
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUpperSemicontinuousLimsupExt.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.upperSemicontinuous_limsupExt : ∀ (Y : Type) [TopologicalSpace Y] (S : Set Y) (u : Y → ℝ), UpperSemicontinuous (GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.limsupExt S u) := by
  first | exact @GlobalTheory.limsupExt_usc_all | exact GlobalTheory.limsupExt_usc_all | (intros; apply GlobalTheory.limsupExt_usc_all <;> assumption)
