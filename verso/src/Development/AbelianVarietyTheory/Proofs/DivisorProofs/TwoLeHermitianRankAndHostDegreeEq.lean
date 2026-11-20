import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.RankHostFacts

/- English proof (translation)
Use `⟨Formalism.L2.Geo.two_le_r D, ?_⟩` and prove the remaining obligations. Unfold `ReciprocityTheory.ChartRestriction.G.FD.fdeg`. Rewrite using `[Formalism.L2.Pj.hostSize_finrank D]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_r_and_fdeg (D : D7) : 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
  refine ⟨Formalism.L2.Geo.two_le_r D, ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
  rw [Formalism.L2.Pj.hostSize_finrank D]
  omega

/- English proof (translation)
The claim follows from `two_le_r_and_fdeg`.
-/
theorem main : ∀ D : D7, 2 ≤ D.R.r ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f :=
  two_le_r_and_fdeg

end GlobalTheory.RankHostFacts
