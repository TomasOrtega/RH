import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackward
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | exact GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.HeckeBackward : CompanionTheory.RgExh.Hk.Back := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | exact GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.BackProof.back <;> assumption)
