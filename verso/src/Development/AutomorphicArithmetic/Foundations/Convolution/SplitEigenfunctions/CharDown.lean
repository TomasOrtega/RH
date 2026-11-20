import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar

open NumberField IsDedekindDomain
open Formalism.L2.Host GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ _ D χ h`. Establish `hE : Module.finrank ℚ E = 2`. Rewrite using `[Module.finrank_eq_card_basis D.b]`. Simplify using the standard rewrite rules. Establish `hθ : D.θ ≠ 0`.

Rewrite using `[← D.b1]`. Conclude with `D.b.ne_zero 1`. Establish `hσ : D.σ ≠ 1`. Introduce `h1`. Establish `h2` using `D.conj`.

Rewrite `h2` using `[h1]`. Establish `h3 : D.θ = -D.θ` using `by simpa using h2`. Establish `h4 : (2 : E) * D.θ = 0` using `by linear_combination h3`. Conclude with `hθ (by simpa using h4)`. Use `A.normChar_of_inv hE χ fun c z => ?_` and prove the remaining obligations.

Break down `GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl` into its components or cases. Rewrite using `[one_smul]`. Establish `h1` using `h z`. Rewrite `h1` using `[map_mul, map_inv, mul_inv_eq_one]`. Establish `h2 : Units.map (D.bar : A E →* A E) z = D.σ • z` using `Units.ext (coe_smul_idele D.σ z).symm`.

Rewrite using `[← h2]`. Conclude with `h1.symm`.
-/
theorem charDown : CharDown := by
  intro E _ _ _ D χ h
  have hE : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b]
    simp
  have hθ : D.θ ≠ 0 := by
    rw [← D.b1]
    exact D.b.ne_zero 1
  have hσ : D.σ ≠ 1 := by
    intro h1
    have h2 := D.conj
    rw [h1] at h2
    have h3 : D.θ = -D.θ := by simpa using h2
    have h4 : (2 : E) * D.θ = 0 := by linear_combination h3
    exact hθ (by simpa using h4)
  refine A.normChar_of_inv hE χ fun c z => ?_
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl
  · rw [one_smul]
  · have h1 := h z
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : Units.map (D.bar : A E →* A E) z = D.σ • z := Units.ext (coe_smul_idele D.σ z).symm
    rw [← h2]
    exact h1.symm

end UpperTheory.ConvolutionTheory.RankTwoDescent
