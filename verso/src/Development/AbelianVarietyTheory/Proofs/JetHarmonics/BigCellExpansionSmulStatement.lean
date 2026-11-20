import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmul
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBigCellExpansionSmul.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.bigCellExpansion_smul : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ), Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  first | exact @GlobalTheory.familyDerivativeExpansion_smul | exact GlobalTheory.familyDerivativeExpansion_smul | (intros; apply GlobalTheory.familyDerivativeExpansion_smul <;> assumption)
