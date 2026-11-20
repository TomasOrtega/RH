import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeG
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsNegHermitianSquareCurvatureBoundedDomainHodgeG.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  first | exact @GlobalTheory.PointFormSign.curv_domGram_isNegSq | exact GlobalTheory.PointFormSign.curv_domGram_isNegSq | (intros; apply GlobalTheory.PointFormSign.curv_domGram_isNegSq <;> assumption)
