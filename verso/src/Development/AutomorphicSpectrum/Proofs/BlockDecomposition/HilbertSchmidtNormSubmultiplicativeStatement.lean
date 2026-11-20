import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicative
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHilbertSchmidtNormSubmultiplicative.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.hilbert_schmidt_norm_submultiplicative : ∀ {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ), Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | exact GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | (intros; apply GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul <;> assumption)
