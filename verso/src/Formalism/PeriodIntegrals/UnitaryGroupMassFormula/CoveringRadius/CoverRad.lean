import Mathlib
import Formalism.PeriodIntegrals.TransferenceCoverRad
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover

open scoped InnerProductSpace

noncomputable section

namespace PI.Tr2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem coverDiv : PI.TransferenceCoverDiv := by
  intro V _ _ _ M hd hspan κ hκ hdual x
  haveI := hd
  haveI : IsZLattice ℝ M := ⟨hspan⟩
  obtain ⟨l, hl, hle⟩ := transference_covering V M κ hκ (fun y hy0 hy => hdual y hy hy0) x
  refine ⟨l, hl, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  linarith

end PI.Tr2
