import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZero
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBigCellExpansionOfBesselFunctionZero.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.familyDerivativeExpansion_of_V_eq_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  first | exact @GlobalTheory.bigCellExpansion_of_besselFunction_zero | exact GlobalTheory.bigCellExpansion_of_besselFunction_zero | (intros; apply GlobalTheory.bigCellExpansion_of_besselFunction_zero <;> assumption)
