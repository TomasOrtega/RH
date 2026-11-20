import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentity
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPartialFractionSquareIdentity.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfDer | exact GlobalTheory.CompanionTheory.RgHeFrame.pfDer | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfDer <;> assumption)
