import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystems
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteJointEigensystems.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.finite_joint_eigenvalues_of_commute : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  first | exact @GlobalTheory.finite_joint_eigensystems | exact GlobalTheory.finite_joint_eigensystems | (intros; apply GlobalTheory.finite_joint_eigensystems <;> assumption)
