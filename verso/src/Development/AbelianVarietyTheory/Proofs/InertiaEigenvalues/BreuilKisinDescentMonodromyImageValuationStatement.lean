import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentMonodromyImageValuation
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LcImage.image_valuation_integralImage` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBreuilKisinDescentMonodromyImageValuation.lean&line=199#L199)
-/
theorem _root_.GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D U ∧ (H + η < l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Valuation l e U η N) ∧ (10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralImage D U) := by
  first | exact @GlobalTheory.LcImage.image_valuation_integralImage | exact GlobalTheory.LcImage.image_valuation_integralImage | (intros; apply GlobalTheory.LcImage.image_valuation_integralImage <;> assumption)
