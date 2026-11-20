import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

/- English proof (translation)
Introduce `D`. Use `⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB D.host, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.BasicNotions.Examples₂.conj_half, Formalism.BasicNotions.Examples₂.conj_bE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaEx_holds : ThetaEx := by
  intro D
  refine ⟨(1 + D.host.sqd) / 2, Formalism.BasicNotions.Examples₂.isIntegral_halfB D.host, ?_⟩
  rw [Formalism.BasicNotions.Examples₂.conj_half, Formalism.BasicNotions.Examples₂.conj_bE]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
