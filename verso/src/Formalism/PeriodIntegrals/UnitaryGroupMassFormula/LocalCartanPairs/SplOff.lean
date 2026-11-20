import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SplPlane
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.PiNonunit

noncomputable section

namespace PI.SqPair.LCP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem split_off_hyperbolic : SplitOff := by
  intro R _ _ _ ι κ _ _ _ _ hc A hA x y hxx hyy hxy
  obtain ⟨u, v, A₁, h1, h2, h3, h4, h5, -, -⟩ := PI.LocCartanPair.splPlane hc A hA x y hxx hyy hxy
  exact ⟨u, v, A₁, h1, h2, h3, h4, h5⟩

end PI.SqPair.LCP
