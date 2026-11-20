import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall

open Complex Metric

noncomputable section

namespace Formalism.ZF

/- English proof (translation)
Establish `h1 : |(s - 1).im| ≤ ‖s - 1‖` using `Complex.abs_im_le_norm _`. Rewrite `h1` using `[Complex.sub_im, Complex.one_im, sub_zero]`. Rewrite using `[norm_div, norm_one, div_le_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma ldr_inv_sub_one_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖1 / (s - 1)‖ ≤ 1 := by
  have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, Complex.one_im, sub_zero] at h1
  rw [norm_div, norm_one, div_le_one (by linarith)]
  linarith

end Formalism.ZF
