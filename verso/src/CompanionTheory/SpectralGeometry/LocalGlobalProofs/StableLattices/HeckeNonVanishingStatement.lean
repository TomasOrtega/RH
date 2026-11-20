import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)
