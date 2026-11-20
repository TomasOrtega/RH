import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZeroBounds

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds
