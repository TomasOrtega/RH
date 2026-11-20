import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormWhittakerGL2LeIntegral
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormWhittakerGL2LeIntegral.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.norm_whittakerGL2_le_integral : ∀ (k : ℕ) (f f' : SchwartzMap (Fin 2 → ℂ) ℂ) (κ : Matrix (Fin 2) (Fin 2) ℂ) (A B D : ℂ),
    A ≠ 0 → D ≠ 0 → ‖κ.det‖ = 1 → (∀ v, f' v = f (Matrix.vecMul v κ)) →
    ‖W2 k f (!![A, B; 0, D] * κ)‖ ≤
      ‖A‖ * ‖D‖⁻¹ * ∫ t : ℂ, (‖t‖ ^ 2)⁻¹ * ‖sF f' (t * A) (t * D)⁻¹‖ := by
  first | exact @GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le | exact GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le | (intros; apply GlobalTheory.CompanionTheory.GodementFE.norm_whittakerGL2_triangular_le <;> assumption)
