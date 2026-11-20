import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace LeadingCovolume

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem periodBasis_of_lt {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : ℕ) (hi : i < g)
    (hi' : i < g + g) : periodBasis τ ⟨i, hi'⟩ = Pi.single (⟨i, hi⟩ : Fin g) 1 := by
  have e : (⟨i, hi'⟩ : Fin (g + g)) = Fin.castAdd g ⟨i, hi⟩ := rfl
  rw [e, periodBasis, Fin.append_left]

end LeadingCovolume

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem LeadingCovolume.proof : LeadingCovolume.Statement := by
  intro g τ r h
  unfold covolume leadMinor
  congr 2
  ext a b
  have ha : (a : ℕ) < g + g := by omega
  have hb : (b : ℕ) < g + g := by omega
  rw [Matrix.of_apply, Matrix.of_apply, dif_pos ⟨ha, hb⟩, periodGram, Matrix.of_apply,
    LeadingCovolume.periodBasis_of_lt τ a (by omega) ha,
    LeadingCovolume.periodBasis_of_lt τ b (by omega) hb]
  rfl

end

end GroundTheory.Heights₂.Heights
