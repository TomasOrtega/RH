import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsFurther
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaAndWindowCount

namespace GlobalTheory.ThinScaleLiterature

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩`.
-/
theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
