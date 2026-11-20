import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranscendenceBasisAlgebraic
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTranscendenceBasisAlgebraic.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_transcendence_basis_algebraic : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (m : ℕ) (a : Fin m → C), ∃ (d : ℕ) (t : Fin d → C), AlgebraicIndependent k t ∧ ∀ j, IsAlgebraic (IntermediateField.adjoin k (Set.range t)) (a j) := by
  first | exact @GlobalTheory.exists_finite_transcendenceBasis_in_family | exact GlobalTheory.exists_finite_transcendenceBasis_in_family | (intros; apply GlobalTheory.exists_finite_transcendenceBasis_in_family <;> assumption)
