import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefectShare.mass_defect_order_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMassDefectOrderLe.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.sumData_mass_be_eq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  first | exact @GlobalTheory.DefectShare.mass_defect_order_le | exact GlobalTheory.DefectShare.mass_defect_order_le | (intros; apply GlobalTheory.DefectShare.mass_defect_order_le <;> assumption)
