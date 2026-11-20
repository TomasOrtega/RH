import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubring
import Mathlib
import Formalism.SatakeDualWeyl.Statement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FStdLatticeMapEqIffMemGLintValuationSubring.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ) (x : GL (Fin r) K), (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) = Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  first | exact @GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | exact GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint | (intros; apply GlobalTheory.GLintLattice.stdLattice_map_eq_iff_mem_GLint <;> assumption)
