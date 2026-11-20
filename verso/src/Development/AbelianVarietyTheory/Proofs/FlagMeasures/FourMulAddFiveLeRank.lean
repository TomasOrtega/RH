import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

/- English proof (translation)
Rewrite using `[X.n_eq]`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `h2` using `D.R.two_le_m`. Take `⟨j, hj⟩` from `D.R.m_even`. Simplify using `only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

/- English proof (translation)
Introduce `D X` and use `⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X, fun u => MassDataLevelSSteps.frameStd_holds X u⟩`.
-/
theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
