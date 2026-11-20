import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Treat this case separately.
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
