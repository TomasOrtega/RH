import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPointsStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgWtMul.evM_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAlgebraicWeightPolyMatrixMultiplicative.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧ ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y → evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  first | exact @GlobalTheory.AlgWtMul.evM_mul | exact GlobalTheory.AlgWtMul.evM_mul | (intros; apply GlobalTheory.AlgWtMul.evM_mul <;> assumption)
