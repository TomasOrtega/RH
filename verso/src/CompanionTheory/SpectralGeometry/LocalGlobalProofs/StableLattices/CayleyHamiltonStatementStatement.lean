import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatement
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | exact GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.CayleyHamiltonHk : CompanionTheory.RgExh.Hk.CayleyHam := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | exact GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.cayleyHam <;> assumption)
