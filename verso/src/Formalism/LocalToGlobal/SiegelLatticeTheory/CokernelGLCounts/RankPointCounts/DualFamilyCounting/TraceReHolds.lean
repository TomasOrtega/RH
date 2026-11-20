import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X t`. Establish `h1 : ∀ v, X.B.I.φ v (X.ιE.symm t) = embS D (X.pl v) t` using `fun v => by`. Rewrite using `[X.φ_eq, RingEquiv.apply_symm_apply]`. Simplify using `only [h1]`. Rewrite using `[Formalism.MainNotions.BlockEstimateWords.trace_tau D t, Finset.sum_div, Equiv.sum_comp X.pl (fun τ => ((embS D τ) t).re)]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_div_cancel_left₀ _ two_ne_zero]`. Both sides reduce to the same expression.
-/
theorem traceRe_holds : TraceRe := by
  intro D X t
  have h1 : ∀ v, X.B.I.φ v (X.ιE.symm t) = embS D (X.pl v) t := fun v => by
    rw [X.φ_eq, RingEquiv.apply_symm_apply]
  simp only [h1]
  rw [Formalism.MainNotions.BlockEstimateWords.trace_tau D t, Finset.sum_div,
    Equiv.sum_comp X.pl (fun τ => ((embS D τ) t).re)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_div_cancel_left₀ _ two_ne_zero]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.CovB
