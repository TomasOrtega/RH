import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianForm
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FSiegelDensitiesOfHermitianForm.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.siegel_densities_of_hermitian_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SiegelDensities F E σ M J := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | exact GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | (intros; apply GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities <;> assumption)
