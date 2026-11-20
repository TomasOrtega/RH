import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjRegularClosureOpen
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjFullRankMeetsRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

/- English proof (translation)
Introduce `K _ ι _ P J n R Ψ V BV hH hC hΨ x hx`. Take `⟨y, hyc, hy⟩` from `hMeet K ι P J n R Ψ V BV hH hC hΨ x hx`. Establish `hO : IsOpen (closure (projRegular R Ψ BV))` using `hOpen K ι P J n R Ψ V BV hH`. Establish `hcl : IsClopen (closure (projRegular R Ψ BV))` using `⟨isClosed_closure, hO⟩`. Rewrite using `[hO.interior_eq]`.

Establish `hsub` using `hcl.connectedComponent_subset (subset_closure hy)`. Rewrite `hsub` using `[← connectedComponent_eq hyc]`. Conclude with `hsub mem_connectedComponent`.
-/
theorem ProjFullRankDense.of_found (hOpen : ProjRegularClosureOpen.Statement)
    (hMeet : ProjFullRankMeetsRegular.Statement) : ProjFullRankDense.Statement := by
  intro K _ ι _ P J n R Ψ V BV hH hC hΨ x hx
  obtain ⟨y, hyc, hy⟩ := hMeet K ι P J n R Ψ V BV hH hC hΨ x hx
  have hO : IsOpen (closure (projRegular R Ψ BV)) := hOpen K ι P J n R Ψ V BV hH
  have hcl : IsClopen (closure (projRegular R Ψ BV)) := ⟨isClosed_closure, hO⟩
  rw [hO.interior_eq]
  have hsub := hcl.connectedComponent_subset (subset_closure hy)
  rw [← connectedComponent_eq hyc] at hsub
  exact hsub mem_connectedComponent

end GroundTheory.Heights₂.Heights.Targets
