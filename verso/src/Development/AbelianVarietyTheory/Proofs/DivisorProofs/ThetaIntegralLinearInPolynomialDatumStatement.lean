import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.ThetaLin.I_lin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaIntegralLinearInPolynomialDatum.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.theta_integral_linear_in_polynomial_datum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ r : ℂ,
      G.M.I om (r • Φ + Ψ) = r • G.M.I om Φ + G.M.I om Ψ := by
  first | exact @GlobalTheory.ThK.ThetaLin.I_lin | exact GlobalTheory.ThK.ThetaLin.I_lin | (intros; apply GlobalTheory.ThK.ThetaLin.I_lin <;> assumption)
