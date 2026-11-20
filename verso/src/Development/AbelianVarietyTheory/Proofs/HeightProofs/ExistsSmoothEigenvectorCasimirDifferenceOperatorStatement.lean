import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FExistsSmoothEigenvectorCasimirDifferenceOperator.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ → (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) → (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) → ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  first | exact @GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | exact GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | (intros; apply GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp <;> assumption)
