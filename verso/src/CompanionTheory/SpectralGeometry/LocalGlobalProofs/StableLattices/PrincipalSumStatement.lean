import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PrincipalSum
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.PrinSumP.prinSum | exact GlobalTheory.CompanionTheory.PrinSumP.prinSum | (intros; apply GlobalTheory.CompanionTheory.PrinSumP.prinSum <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.PrincipalSum : CompanionTheory.RgExh.Hk.PrinSum := by
  first | exact @GlobalTheory.CompanionTheory.PrinSumP.prinSum | exact GlobalTheory.CompanionTheory.PrinSumP.prinSum | (intros; apply GlobalTheory.CompanionTheory.PrinSumP.prinSum <;> assumption)
