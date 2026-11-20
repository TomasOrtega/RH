import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesDiagGram

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem embVec_single {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by
  funext y
  simp only [embVec, Pi.single_apply]
  split_ifs <;> simp

end KLinesDiagGram

open KLinesDiagGram in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem LinesDiagGram.proof : LinesDiagGram.Statement := by
  intro K _ n d σ k τ hτ
  ext j j'
  simp only [gramAt, embVec_single, Matrix.diagonal_apply]
  rw [show (star (Pi.single (τ j) (1 : ℂ)) : Fin n → ℂ) = Pi.single (τ j) 1 by
    funext y; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp]
  rw [single_dotProduct, one_mul, Matrix.mulVec_diagonal]
  simp only [Pi.single_apply, hτ.eq_iff]
  split_ifs with h
  · subst h; simp
  · simp

end GroundTheory.Heights₂.Heights
