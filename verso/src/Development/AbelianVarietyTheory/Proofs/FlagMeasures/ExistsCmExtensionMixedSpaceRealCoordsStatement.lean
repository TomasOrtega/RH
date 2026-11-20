import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCmExtensionMixedSpaceRealCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsCmExtensionMixedSpaceRealCoords.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : mixedEmbedding.mixedSpace F ≃L[ℝ] (InfinitePlace E → ℝ), MeasurePreserving e volume volume ∧ ∀ y : F, e (mixedEmbedding F y) = reV (algebraMap F E y) := by
  first | exact @GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | exact GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords | (intros; apply GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords <;> assumption)
