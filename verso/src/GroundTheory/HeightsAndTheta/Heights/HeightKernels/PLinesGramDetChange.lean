import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

/- English proof (translation)
Introduce `K _ n h σ ι _ _ B u`. Establish `hu : u = fun a => ∑ b, B.toMatrix u b a • B b`. Use function extensionality and compare the values at `a`. Conclude with `(B.sum_toMatrix_smul_self u a).symm`. Establish `hg` using `h1 K n h σ ι (⇑B) (B.toMatrix u)`.

Rewrite `hg` using `[← hu]`. Rewrite using `[hg, det_mul, det_mul, det_conjTranspose, RingHom.map_det]`. Simplify using `only [RingHom.mapMatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LinesGramDetChange.proof (h1 : LinesGramChange.Statement) :
    LinesGramDetChange.Statement := by
  intro K _ n h σ ι _ _ B u
  have hu : u = fun a => ∑ b, B.toMatrix u b a • B b := by
    funext a
    exact (B.sum_toMatrix_smul_self u a).symm
  have hg := h1 K n h σ ι (⇑B) (B.toMatrix u)
  rw [← hu] at hg
  rw [hg, det_mul, det_mul, det_conjTranspose, RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

end GroundTheory.Heights₂.Heights
