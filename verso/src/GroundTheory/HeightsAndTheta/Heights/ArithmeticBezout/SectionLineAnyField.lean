import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial LineChowForm

noncomputable section

namespace SectionLine

variable (F : Type) [Field F]

def coeffX0Alt : Fin 2 → F := fun j => if j = 0 then 1 else 0

def coeffX1 : Fin 2 → F := fun j => if j = 0 then 0 else 1

def pointChowForm : MvPolynomial (Fin 1 × Fin 2) F := X (0, 1)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem linearForm_coeffX1 : linForm (coeffX1 F) = (X 1 : MvPolynomial (Fin 2) F) := by
  simp [linForm, coeffX1, Fin.sum_univ_two]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem linearFormX1_ne_zero : linForm (coeffX1 F) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) F)) := by
  rw [linearForm_coeffX1, Ideal.mem_bot]
  exact X_ne_zero 1

end SectionLine

end

end GroundTheory.Heights₂.Heights
