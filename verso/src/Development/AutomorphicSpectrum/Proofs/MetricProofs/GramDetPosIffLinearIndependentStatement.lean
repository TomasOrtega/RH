import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosIffLinearIndependent
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGramDetPosIffLinearIndependent.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.gram_det_pos_iff_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (LinearIndependent ℂ u → 0 < (R.gram u).det.re ∧ (R.gram u).det.im = 0) ∧ ((R.gram u).det ≠ 0 → LinearIndependent ℂ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramPos.gram_det_pos_iff <;> assumption)
