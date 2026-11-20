import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSigns
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgHeSign.pfSign` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPartialFractionCoefficientSigns.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.partial_fraction_coefficient_signs : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧ ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  first | exact @GlobalTheory.CompanionTheory.RgHeSign.pfSign | exact GlobalTheory.CompanionTheory.RgHeSign.pfSign | (intros; apply GlobalTheory.CompanionTheory.RgHeSign.pfSign <;> assumption)
