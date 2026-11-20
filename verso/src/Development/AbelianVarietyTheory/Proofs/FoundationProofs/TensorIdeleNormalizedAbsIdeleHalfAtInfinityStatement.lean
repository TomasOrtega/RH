import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Eis.Conv.absE_halfE` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTensorIdeleNormalizedAbsIdeleHalfAtInfinity.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  first | exact @GlobalTheory.Eis.Conv.absE_halfE | exact GlobalTheory.Eis.Conv.absE_halfE | (intros; apply GlobalTheory.Eis.Conv.absE_halfE <;> assumption)
