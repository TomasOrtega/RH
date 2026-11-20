import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescends
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.matrix_system_nonzero_solution_descends` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMatrixSystemNonzeroSolutionDescends.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  first | exact @GlobalTheory.matrix_system_nonzero_solution_descends | exact GlobalTheory.matrix_system_nonzero_solution_descends | (intros; apply GlobalTheory.matrix_system_nonzero_solution_descends <;> assumption)
