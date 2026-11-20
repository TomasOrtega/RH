import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem idxFull_of (hMono : IdxMono) (hSc : IdxScaleIn) : IdxFull := by
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _hThM σ hσ hsc E r hE
  obtain ⟨hlat, heq⟩ := hSc K Z w ⊤ M ThK hM hThK σ hσ
  have hmono : lix w M (sc σ ThK) ≤ lix w M Th := hMono K Z w ⊤ M Th (sc σ ThK) hM hTh hlat hsc
  have hm : (lix w M (sc σ ThK) : ℝ) ≤ (lix w M Th : ℝ) := by exact_mod_cast hmono
  have hv : (lix w M (sc σ ThK) : ℝ) = (lix w M ThK : ℝ) + (finrank K Z : ℝ) * (vw w σ : ℝ) := by
    rw [heq]
    push_cast
    rw [finrank_top]
  linarith

end Formalism.EigenvalueLevelCeiling
