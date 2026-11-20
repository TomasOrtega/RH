import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MMatEntryMeasurable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X u μ ν hμ hν`. Take `⟨hσ, h0, hc, hi⟩` from `hμ`. Take `⟨hσ', h0', hc', hi'⟩` from `hν`. Use `haveI := hσ`. Use `haveI := hσ'`.

Establish `hco : (ProductExactness.NinfG X u : Set X.B.I.Ginf) = X.NinfU u` using `ProductExactness.NinfG_coe X u`. Rewrite `hc`, `hi`, `hc'`, `hi'` using `[← hco]`. Take `⟨κ, -, -, hκ⟩` from `ProductExactness.PiM.uniq_on_closed (ProductExactness.NinfG X u) (ProductExactness.NinfG_closed X u) μ ν hc hc' hi hi' h0 h0'`. Conclude with `⟨κ, hκ⟩`.
-/
theorem haarUnique_holds : Formalism.L2.SG.Pf.LsNc5.HaarUnique := by
  intro D X u μ ν hμ hν
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  obtain ⟨hσ', h0', hc', hi'⟩ := hν
  haveI := hσ
  haveI := hσ'
  have hco : (ProductExactness.NinfG X u : Set X.B.I.Ginf) = X.NinfU u := ProductExactness.NinfG_coe X u
  rw [← hco] at hc hi hc' hi'
  obtain ⟨κ, -, -, hκ⟩ := ProductExactness.PiM.uniq_on_closed (ProductExactness.NinfG X u) (ProductExactness.NinfG_closed X u) μ ν hc hc' hi hi' h0 h0'
  exact ⟨κ, hκ⟩

end Formalism.L2.SG.Pf.NcReal.JX
