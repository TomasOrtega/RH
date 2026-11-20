import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogFactorialPowMulFactorialPowLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLogFactorialPowMulFactorialPowLe.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' : ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R → Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  first | exact @GlobalTheory.log_factorial_pow_mul_factorial_pow_le | exact GlobalTheory.log_factorial_pow_mul_factorial_pow_le | (intros; apply GlobalTheory.log_factorial_pow_mul_factorial_pow_le <;> assumption)
