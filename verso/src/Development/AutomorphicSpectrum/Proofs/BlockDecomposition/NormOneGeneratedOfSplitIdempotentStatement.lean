import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfSplitIdempotent
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormOneGeneratedOfSplitIdempotent.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.norm_one_generated_of_split_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split | exact GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split | (intros; apply GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split <;> assumption)
