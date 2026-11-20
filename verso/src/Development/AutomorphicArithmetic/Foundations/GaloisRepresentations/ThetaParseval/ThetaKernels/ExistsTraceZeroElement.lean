import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtensionStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNeZeroConjNegK

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FFoundations%2FGaloisRepresentations%2FThetaParseval%2FThetaKernels%2FExistsNeZeroConjNegK.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_trace_zero_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @_root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | exact _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k | (intros; apply _root_.GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg_k <;> assumption)
end
