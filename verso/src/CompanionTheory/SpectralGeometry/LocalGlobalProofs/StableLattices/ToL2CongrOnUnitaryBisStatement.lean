import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToL2CongrOnUnitaryBis
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.PackEmb.pack | exact GlobalTheory.CompanionTheory.PackEmb.pack | (intros; apply GlobalTheory.CompanionTheory.PackEmb.pack <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rgExh_pack : CompanionTheory.RgExh.Dec.L.Pack := by
  first | exact @GlobalTheory.CompanionTheory.PackEmb.pack | exact GlobalTheory.CompanionTheory.PackEmb.pack | (intros; apply GlobalTheory.CompanionTheory.PackEmb.pack <;> assumption)
