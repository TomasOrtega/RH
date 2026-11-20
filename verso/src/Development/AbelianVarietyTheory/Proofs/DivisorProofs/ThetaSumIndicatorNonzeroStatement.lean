import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzero
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaSumIndicatorNonzero.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.theta_sum_indicator_nonzero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | exact GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | (intros; apply GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero <;> assumption)
