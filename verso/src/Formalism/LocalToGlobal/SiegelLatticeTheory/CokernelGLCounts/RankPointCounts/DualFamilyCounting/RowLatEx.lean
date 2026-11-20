import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal

namespace Formalism.L2.SG.Pf.Cnt

/- English proof (translation)
Introduce `D T u`. Take `⟨Λ, hΛ⟩` from `Formalism.L2.SG.Pf.latSub T.X u 1`. Conclude with `⟨Λ, Formalism.L2.SG.Pf.latRowLat T.X u 1 Λ hΛ⟩`.
-/
theorem lattice_exists_holds : RowLatExists := by
  intro D T u
  obtain ⟨Λ, hΛ⟩ := Formalism.L2.SG.Pf.latSub T.X u 1
  exact ⟨Λ, Formalism.L2.SG.Pf.latRowLat T.X u 1 Λ hΛ⟩

end Formalism.L2.SG.Pf.Cnt
