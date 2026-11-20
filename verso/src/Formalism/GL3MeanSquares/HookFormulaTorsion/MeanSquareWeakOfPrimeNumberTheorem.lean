import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareOfPrimeNumberTheorem

noncomputable section

namespace Formalism.HermitianLattices.WeakMeanSquareEstimates

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mean_square_weak_of_prime_number_theorem : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ MeanSquareHypW ε C x₀ :=
  Formalism.HermitianLattices.PrimeNumberTheoremConsequences.mean_square_of_prime_number_theorem

end Formalism.HermitianLattices.WeakMeanSquareEstimates
