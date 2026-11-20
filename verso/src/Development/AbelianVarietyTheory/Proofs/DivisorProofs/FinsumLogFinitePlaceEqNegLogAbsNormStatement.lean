import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogFinitePlaceEqNegLogAbsNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinsumLogFinitePlaceEqNegLogAbsNorm.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | exact GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | (intros; apply GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm <;> assumption)
