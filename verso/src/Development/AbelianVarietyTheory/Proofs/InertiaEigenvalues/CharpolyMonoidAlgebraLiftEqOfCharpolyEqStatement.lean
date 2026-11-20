import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
import Mathlib
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharpolyMonoidAlgebraLiftEqOfCharpolyEq.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.charpoly_monoidAlgebraLift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∀ a : MonoidAlgebra k G, (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly = (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  first | exact @GlobalTheory.charpoly_lift_eq_of_charpoly_eq | exact GlobalTheory.charpoly_lift_eq_of_charpoly_eq | (intros; apply GlobalTheory.charpoly_lift_eq_of_charpoly_eq <;> assumption)
