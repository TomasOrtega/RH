import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

open Formalism.REAL (fockF)

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Rewrite using `[Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_comm (starRingEnd ℂ _)]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
lemma LFockb_fockF_self {σ : Type*} (f : MvPolynomial σ ℂ) :
    fockF f f = ((∑ m ∈ f.support, Complex.normSq (f.coeff m) *
      ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, mul_comm (starRingEnd ℂ _)]
  push_cast
  rfl

end Formalism.GradedWeylDivisibility
