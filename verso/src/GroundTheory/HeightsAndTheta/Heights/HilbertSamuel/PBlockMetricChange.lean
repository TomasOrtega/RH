import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ I d d' hI hy hk`. Establish `hdeg : d'.A.a = unitDeg d.k₀` using `hk ▸ d'.deg`. Establish `hle : d'.P0 ≤ mCoordIdeal d.y` using `hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line`. Establish `hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A` using `hy ▸ d'.semipos`. Establish `h1` using `hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl`.

Establish `h2` using `hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI`. Use `(h1.add h2).congr_left fun n => ?_` and prove the remaining obligations. Simplify using `only [hsDefect, hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
