import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SimilExists.exists_similitude` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSimilitudeBetweenNonemptySpheres.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.similitude_between_nonempty_spheres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  first | exact @GlobalTheory.CompanionTheory.SimilExists.exists_similitude | exact GlobalTheory.CompanionTheory.SimilExists.exists_similitude | (intros; apply GlobalTheory.CompanionTheory.SimilExists.exists_similitude <;> assumption)
