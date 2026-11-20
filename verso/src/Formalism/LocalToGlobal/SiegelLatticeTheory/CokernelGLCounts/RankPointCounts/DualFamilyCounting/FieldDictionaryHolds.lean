import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D`. Use `⟨D.sp.cm.cmUnram, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[D.sp.cm.fixed a, RingHom.mem_range, Set.mem_range]`. Introduce `x hx`.

Conclude with `(D.sp.Y 0).nondeg.1 x hx`.
-/
theorem field_dictionary_holds : HostDict := by
  intro D
  refine ⟨D.sp.cm.cmUnram, ?_, ?_⟩
  · intro a
    rw [D.sp.cm.fixed a, RingHom.mem_range, Set.mem_range]
  · intro x hx
    exact (D.sp.Y 0).nondeg.1 x hx

end Formalism.L2.SG.Pf.Cnt
