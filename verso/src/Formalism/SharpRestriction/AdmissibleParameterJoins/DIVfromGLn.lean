import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLf

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem family_four_choice_conditions {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) (h : ChosenE Fm C0 CH) : LocalQuadraticParts.ChosenLeadingTermsCountFamily Fm := by
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact h.2.1

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem family_bad_choice_bound {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) (h : ChosenE Fm C0 CH) : LocalQuadraticParts.FewBadOrbitsFamily Fm := by
  obtain ⟨_, _, Cb, _, _, hb, h⟩ := h
  exact ⟨Cb, hb, h.2.2.1⟩

end Formalism.MainNotions.J

end
