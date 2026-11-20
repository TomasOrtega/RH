import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FContinuousIsotropicSandwichMeanTranslation.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.continuous_isotropicSandwichMean_translation : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → Continuous (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F) := by
  first | exact @GlobalTheory.IsoMean.continuous_meanX | exact GlobalTheory.IsoMean.continuous_meanX | (intros; apply GlobalTheory.IsoMean.continuous_meanX <;> assumption)
