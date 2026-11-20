import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorInvolutionInvolutive
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTensorInvolutionInvolutive.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.tensor_involution_involutive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | exact GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | (intros; apply GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq <;> assumption)
