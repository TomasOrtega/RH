import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsBorelEigenvectorOfPolynomialRepGLComplex.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam := by
  first | exact @GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isBEig_of_isPolyRep <;> assumption)
