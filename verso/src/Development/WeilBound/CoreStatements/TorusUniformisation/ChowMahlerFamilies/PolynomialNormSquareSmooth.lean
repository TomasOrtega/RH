import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial

namespace PositivityTheory.Xgn.SmoothPolynomialNormSquare

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [MvPolynomial.eval_C]`. Conclude with `contDiff_const`. Consider the case `add p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.mul (contDiff_apply ℝ ℂ i)`.
-/
theorem contDiff_eval (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_apply ℝ ℂ i)

end PositivityTheory.Xgn.SmoothPolynomialNormSquare

/- English proof (translation)
Introduce `σ _ s`. Conclude with `(PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ`.
-/
theorem PositivityTheory.Xgn.polynomial_norm_square_smooth : ∀ (σ : Type) [Fintype σ] (s : MvPolynomial σ ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) s)‖ ^ 2) := by
  intro σ _ s
  exact (PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ
