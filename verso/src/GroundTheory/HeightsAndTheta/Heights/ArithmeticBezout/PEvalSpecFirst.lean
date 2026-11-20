import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `n k f v w`. Express the relevant statement in the definitionally equal form `eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) = eval₂Hom (RingHom.id ℂ) (consGroup v w) f`. Rewrite using `[eval₂Hom_bind₁]`. Use `congr 2`. Use function extensionality and compare the values at `ij`.

Take `⟨i, j⟩` from `ij`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [specFirstVar, consGroup]`. Consider the case `succ i => simp [specFirstVar, consGroup]`.
-/
theorem EvalSpecFirst.proof : EvalSpecFirst.Statement := by
  intro n k f v w
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (specFirstVar v) f) =
    eval₂Hom (RingHom.id ℂ) (consGroup v w) f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar, consGroup]
  | succ i => simp [specFirstVar, consGroup]

end GroundTheory.Heights₂.Heights
