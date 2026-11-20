import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

/- English proof (translation)
Establish `: FiniteDimensional ℚ E` using `inferInstance`. Establish `: Algebra.IsAlgebraic ℚ E` using `Algebra.IsAlgebraic.of_finite ℚ E`. Establish `: Nonempty (E →ₐ[ℚ] ℂ)` using `⟨IsAlgClosed.lift⟩`. Conclude with `Nat.card_pos`.
-/
theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

/- English proof (translation)
Introduce `T _ K' _ _ y hP`. Rewrite using `[IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]`. Conclude with `PointDegreeComplexPositive.card_algHom_pos _`.
-/
theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
