import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PI.PoincareSeriesFinite.UnitaryGroupMassFormula

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

/- English proof (translation)
Unfold `quotientLIntegral multiplicityLIntegral`. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `PI.FoldMult.UnitaryGroupMassFormula.one_le_mult Γ Ω h1 y`.
-/
theorem quotientLIntegral_le_multiplicityLIntegral {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] (μ : Measure G) (Γ : Subgroup G) (Ω : Set G)
    (h1 : (1 : G) ∈ Ω) (F : Set G) (Ph : G → ℂ) :
    quotientLIntegral μ F Ph ≤ multiplicityLIntegral μ Γ Ω F Ph := by
  unfold quotientLIntegral multiplicityLIntegral
  refine lintegral_mono fun y => ?_
  calc ‖Ph y‖ₑ = 1 * ‖Ph y‖ₑ := (one_mul _).symm
    _ ≤ mult Γ Ω y * ‖Ph y‖ₑ := by
      gcongr
      exact PI.FoldMult.UnitaryGroupMassFormula.one_le_mult Γ Ω h1 y

/- English proof (translation)
Introduce `Γ S hΓ hSΓ Ω hΩ h1 a Ph hPh F hF hL D hD x`. Use `haveI := hΓ`. Use `lt_of_le_of_lt (foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.isClosed.measurableSet a Ph hPh.1 hPh.2.1 hPh.2.2 F hF D hD x) ?_` and prove the remaining obligations. Use `ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top (PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top Γ Ω hΩ x)) ?_` and prove the remaining obligations. Conclude with `lt_of_le_of_lt (quotientLIntegral_le_multiplicityLIntegral μ Γ Ω h1 F Ph) hL`.
-/
theorem poincareSeriesFinite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesFinite G μ := by
  intro Γ S hΓ hSΓ Ω hΩ h1 a Ph hPh F hF hL D hD x
  haveI := hΓ
  refine lt_of_le_of_lt (foldBound_holds G μ Γ S hΓ hSΓ Ω hΩ.isClosed.measurableSet a Ph hPh.1 hPh.2.1
    hPh.2.2 F hF D hD x) ?_
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (PI.FoldMult.UnitaryGroupMassFormula.mult_lt_top Γ Ω hΩ x)) ?_
  exact lt_of_le_of_lt (quotientLIntegral_le_multiplicityLIntegral μ Γ Ω h1 F Ph) hL

end PI.PoincareSeriesFinite.UnitaryGroupMassFormula
