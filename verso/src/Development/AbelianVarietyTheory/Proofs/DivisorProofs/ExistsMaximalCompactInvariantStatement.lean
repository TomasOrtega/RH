import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThKAutV.isAut_thetaIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMaximalCompactInvariant.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_maximal_compact_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThKAutV.isAut_thetaIntegral | exact GlobalTheory.ThKAutV.isAut_thetaIntegral | (intros; apply GlobalTheory.ThKAutV.isAut_thetaIntegral <;> assumption)
