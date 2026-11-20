import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)
