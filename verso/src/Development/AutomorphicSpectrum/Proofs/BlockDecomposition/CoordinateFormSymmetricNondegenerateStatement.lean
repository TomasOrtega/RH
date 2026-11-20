import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoordinateFormSymmetricNondegenerate.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.coordinate_form_symmetric_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero <;> assumption)
