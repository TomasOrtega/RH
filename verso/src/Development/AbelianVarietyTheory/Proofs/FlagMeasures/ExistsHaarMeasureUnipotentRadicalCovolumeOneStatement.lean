import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsHaarMeasureUnipotentRadicalCovolumeOne.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  first | exact @GlobalTheory.NsubHaarCovol.exists_haar_covol_one | exact GlobalTheory.NsubHaarCovol.exists_haar_covol_one | (intros; apply GlobalTheory.NsubHaarCovol.exists_haar_covol_one <;> assumption)
