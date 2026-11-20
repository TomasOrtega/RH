import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc.W

/- English proof (translation)
Introduce `F E _ _ _ _ _ n σ J v Lb T hfin hint hdual hT y`. Conclude with `⟨fun hy z hz => hF F E n σ J v Lb hint y hy z hz, fun h => hB F E n σ J v Lb T hfin hint hdual hT y h⟩`.
-/
theorem selfDualLoc_of_dirs (hF : FwdDir) (hB : BwdDir) : PI.SelfDualLoc := by
  intro F E _ _ _ _ _ n σ J v Lb T hfin hint hdual hT y
  exact ⟨fun hy z hz => hF F E n σ J v Lb hint y hy z hz,
    fun h => hB F E n σ J v Lb T hfin hint hdual hT y h⟩

end PI.SelfDualLoc.W
