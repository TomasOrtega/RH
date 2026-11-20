import Mathlib
import Formalism.PeriodIntegrals.TransferenceCoverRad
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover

open scoped InnerProductSpace

noncomputable section

namespace PI.Tr2

/- English proof (translation)
Introduce `V _ _ _ M hd hspan κ hκ hdual x`. Use `haveI := hd`. Use `haveI : IsZLattice ℝ M := ⟨hspan⟩`. Take `⟨l, hl, hle⟩` from `transference_covering V M κ hκ (fun y hy0 hy => hdual y hy hy0) x`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
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
