import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Places
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPlaces_thW'_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) : Gen.IsPlaces σ B.ψ (thW B) (fun _ => -1) := by
  have : IsTotallyReal F := hB.cm.1
  refine ⟨fun w => GlobalTheory.Mem.VolExists.infEmb_continuous (thW_infEmb B w),
    GlobalTheory.Mem.VolExists.infEmb_bijective hB.cm (isCMFam_conj B hB.cm) (fun w => thW_infEmb B w),
    fun w z => GlobalTheory.Mem.VolExists.infEmb_sigR hB.cm (thW_infEmb B w) z, fun _ => by norm_num, fun x => ?_⟩
  have hs := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).2.2 (archimedeanEmbeddingTensor B) (archimedean_embedding_family B) x
  have hs' : B.ψ ((x, 0) : AF F) = _ := hs
  change B.ψ ((x, 0) : AF F) = _
  rw [hs']
  congr 1
  have hr : ∀ w, starRingEnd ℂ (archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E))) = archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E)) := fun w => by
    rw [archimedean_embedding_tmul, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      Complex.conj_ofReal]
  simp only [thW_eq, hr]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
