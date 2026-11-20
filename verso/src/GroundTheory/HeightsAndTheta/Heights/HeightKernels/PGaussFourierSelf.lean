import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory
open scoped FourierTransform

namespace PGaussFourierSelf

/- English proof (translation)
Rewrite using `[Complex.ofReal_exp]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
lemma ofReal_gauss {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end PGaussFourierSelf

/- English proof (translation)
Introduce `g w`. Establish `hb : 0 < (π : ℂ).re` using `by simpa using Real.pi_pos`. Establish `hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) = fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2)`. Use function extensionality and compare the values at `x`. Conclude with `PGaussFourierSelf.ofReal_gauss x`.

Rewrite using `[hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]`. Establish `hpi : (π : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`. Rewrite using `[div_self hpi, Complex.one_cpow, one_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem GaussFourierSelf.proof : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end GroundTheory.Heights₂.Heights
