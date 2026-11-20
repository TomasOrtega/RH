import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixPolynomialDetNormFixedPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionMatrix.exists_padic_matrix` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FMatrixPolynomialDetNormFixedPoints.lean&line=324#L324)
-/
theorem _root_.GlobalTheory.T.matrix_polynomial_det_norm_fixed_points : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q] (s : Module.End ℤ Q), (∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) → ∃ U : Matrix (Fin m) (Fin m) ℤ_[l], (∀ F : Polynomial ℤ, Finite {x : Q // Polynomial.aeval s F x = 0} → ‖(Polynomial.aeval U F).det‖ = ‖((Nat.card {x : Q // Polynomial.aeval s F x = 0} : ℕ) : ℚ_[l])‖) ∧ (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ∀ (j : ℕ) (x : Q), l ^ j • x = 0 → Polynomial.aeval s F x = 0) ∧ ∀ (j : ℕ) (pt : Fin m → Q) (Mat : Matrix (Fin m) (Fin m) (ZMod (l ^ j))), (∀ i, l ^ j • pt i = 0) → (∀ y : Q, l ^ j • y = 0 → ∃! c : Fin m → ZMod (l ^ j), ∑ i, (c i).val • pt i = y) → (∀ i, s (pt i) = ∑ i', (Mat i' i).val • pt i') → PadicInt.toZModPow j U.det = Mat.det := by
  first | exact @GlobalTheory.TorsionMatrix.exists_padic_matrix | exact GlobalTheory.TorsionMatrix.exists_padic_matrix | (intros; apply GlobalTheory.TorsionMatrix.exists_padic_matrix <;> assumption)
