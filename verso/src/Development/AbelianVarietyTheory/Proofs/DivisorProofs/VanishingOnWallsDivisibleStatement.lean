import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnWallsDivisible
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagPoly.eq_delPol_mul_invForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVanishingOnWallsDivisible.lean&line=224#L224)
-/
theorem _root_.GlobalTheory.T.vanishing_on_walls_divisible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (P : Pol ι N), P.IsHomogeneous (dimFl ι N + 1) → AntiL j P → (∀ (τ : ι) (a b : Fin N), (a : ℕ) < j → j ≤ (b : ℕ) → ∃ U : Set (ι → Fin N → ℝ), IsOpen U ∧ (∃ x ∈ U, x τ a = x τ b) ∧ ∀ x ∈ U, x τ a = x τ b → ev x P = 0) → ∃ al be : ι → ℝ, P = delPol ι N * invForm j al be := by
  first | exact @GlobalTheory.FlagPoly.eq_delPol_mul_invForm | exact GlobalTheory.FlagPoly.eq_delPol_mul_invForm | (intros; apply GlobalTheory.FlagPoly.eq_delPol_mul_invForm <;> assumption)
