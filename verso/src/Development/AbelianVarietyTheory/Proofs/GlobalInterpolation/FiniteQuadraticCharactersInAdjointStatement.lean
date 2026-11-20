import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuadraticCharactersInAdjoint
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FFiniteQuadraticCharactersInAdjoint.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.finite_quadratic_characters_in_adjoint' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k), Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  first | exact @GlobalTheory.finite_quadratic_characters_in_adjoint | exact GlobalTheory.finite_quadratic_characters_in_adjoint | (intros; apply GlobalTheory.finite_quadratic_characters_in_adjoint <;> assumption)
