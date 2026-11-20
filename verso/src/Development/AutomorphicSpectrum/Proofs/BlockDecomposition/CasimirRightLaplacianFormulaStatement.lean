import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCasimirRightLaplacianFormula.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.casimir_right_laplacian_formula : ∀ {n : ℕ} (E : KMod n), ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.om_section | exact GlobalTheory.CompanionTheory.WaveSpd.om_section | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.om_section <;> assumption)
