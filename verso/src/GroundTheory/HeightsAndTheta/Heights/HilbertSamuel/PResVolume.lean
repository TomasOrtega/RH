import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmoothChartVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

/- English proof (translation)
Introduce `K _ ι _ P J e R _ _ hP`. Take `⟨z, hzP, hzJ⟩` from `exists_mcPts_not_mem_mcPts hP R.nondeg`. Take `⟨x, -⟩` from `R.surj z hzP hzJ`. Establish `: Nonempty R.X` using `⟨x⟩`. Conclude with `ChartVolume.exists_isSmoothVolume R.A`.
-/
theorem ResVolume.proof : ResVolume.Statement := by
  intro K _ ι _ P J e R _ _ hP
  obtain ⟨z, hzP, hzJ⟩ := exists_mcPts_not_mem_mcPts hP R.nondeg
  obtain ⟨x, -⟩ := R.surj z hzP hzJ
  have : Nonempty R.X := ⟨x⟩
  exact ChartVolume.exists_isSmoothVolume R.A

end GroundTheory.Heights₂.Heights.HilbertSamuel
