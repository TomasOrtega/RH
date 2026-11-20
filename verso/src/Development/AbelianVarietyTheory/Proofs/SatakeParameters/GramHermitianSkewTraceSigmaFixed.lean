import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
open Matrix

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_hermitian_and_trace_fixed :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, σ (σ x) = x) → σ δ = -δ →
  ∀ (n' r : ℕ) (JT : GL (Fin n') L) (z : Matrix (Fin n') (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ k j, σ (Γ k j) = - Γ j k) →
  (∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) = (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j) ∧
  σ (δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z))) =
    δ * Matrix.trace (Γ * (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z)) := by
  intro L _ _ σ δ hσ hδ n' r JT z Γ hJ hΓ
  have h1 : ∀ j k, σ ((Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) j k) =
      (Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z) k j := by
    intro j k
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul, hσ, hJ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  refine ⟨h1, ?_⟩
  generalize Formalism.UG.cT σ z * (JT : Matrix (Fin n') (Fin n') L) * z = G at h1 ⊢
  have h2 : σ (Matrix.trace (Γ * G)) = - Matrix.trace (Γ * G) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hΓ, h1,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [map_mul, hδ, h2]
  ring

end GlobalTheory
