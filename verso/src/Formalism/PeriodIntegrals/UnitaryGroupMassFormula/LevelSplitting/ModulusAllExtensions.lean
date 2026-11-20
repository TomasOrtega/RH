import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousFirstOrbitMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne

noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)`. Introduce `_ _ g μ hμ`. Conclude with `pres_snd (InfiniteAdeleRing F) (Af F) σ J (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ`.
-/
theorem modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ

/- English proof (translation)
The claim follows from `modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds`.
-/
theorem modulus_all_extensions : PI.LevelKSplit.W.CD.ModVAll :=
  modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds

end PI.LevelKSplit.W.MVA
