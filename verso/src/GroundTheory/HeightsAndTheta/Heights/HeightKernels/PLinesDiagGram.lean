import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesDiagGram

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [embVec, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem embVec_single {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by
  funext y
  simp only [embVec, Pi.single_apply]
  split_ifs <;> simp

end KLinesDiagGram

open KLinesDiagGram in

/- English proof (translation)
Introduce `K _ n d σ k τ hτ`. Use extensionality with `j j'`. Simplify using `only [gramAt, embVec_single, Matrix.diagonal_apply]`. Rewrite using `[show (star (Pi.single (τ j) (1 : ℂ)) : Fin n → ℂ) = Pi.single (τ j) 1 by`. Apply the tactic sequence `funext y; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp]`.

Rewrite using `[single_dotProduct, one_mul, Matrix.mulVec_diagonal]`. Simplify using `only [Pi.single_apply, hτ.eq_iff]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
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
