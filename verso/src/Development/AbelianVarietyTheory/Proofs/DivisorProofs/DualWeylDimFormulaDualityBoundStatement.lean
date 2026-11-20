import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylDimFormulaDualityBound
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeylDimBound.dim_weyl_dual_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualWeylDimFormulaDualityBound.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.dualWeyl_dim_formula_duality_bound : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) ∧ (∀ s : ℕ, (∀ i, la i ≤ s) → dim (fun i => s - la (Fin.rev i)) = dim la) ∧ ∀ w : ℤ, (dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  first | exact @GlobalTheory.WeylDimBound.dim_weyl_dual_bound | exact GlobalTheory.WeylDimBound.dim_weyl_dual_bound | (intros; apply GlobalTheory.WeylDimBound.dim_weyl_dual_bound <;> assumption)
