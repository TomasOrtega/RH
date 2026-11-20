import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumns
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryMinorLeOneAndHadamardColumns.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns : (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n), ‖(u.1.submatrix I J).det‖ ≤ 1) ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ), ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  first | exact @GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | exact GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | (intros; apply GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard <;> assumption)
