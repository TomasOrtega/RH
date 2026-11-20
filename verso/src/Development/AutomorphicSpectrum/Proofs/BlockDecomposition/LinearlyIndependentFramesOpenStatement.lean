import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLinearlyIndependentFramesOpen.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.linearly_independent_frames_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free <;> assumption)
