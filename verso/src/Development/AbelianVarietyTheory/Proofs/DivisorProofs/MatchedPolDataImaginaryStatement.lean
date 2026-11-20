import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolDataImaginary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThKAutKInf.isAut_thetaIntegral_of_le_kInf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatchedPolDataImaginary.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.matched_pol_data_imaginary : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      ∀ K : Subgroup (GAd σ (c • G.W.J.map σ)), (∀ x ∈ K, (toGAd hσ G.W.J hc).symm x ∈ KInf σ G.W B.emb) →
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThKAutKInf.isAut_thetaIntegral_of_le_kInf | exact GlobalTheory.ThKAutKInf.isAut_thetaIntegral_of_le_kInf | (intros; apply GlobalTheory.ThKAutKInf.isAut_thetaIntegral_of_le_kInf <;> assumption)
