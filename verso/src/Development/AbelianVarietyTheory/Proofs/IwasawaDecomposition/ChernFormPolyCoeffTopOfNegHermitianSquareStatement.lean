import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PointFormSign.chernPoly_top_of_negSq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FChernFormPolyCoeffTopOfNegHermitianSquare.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  first | exact @GlobalTheory.PointFormSign.chernPoly_top_of_negSq | exact GlobalTheory.PointFormSign.chernPoly_top_of_negSq | (intros; apply GlobalTheory.PointFormSign.chernPoly_top_of_negSq <;> assumption)
