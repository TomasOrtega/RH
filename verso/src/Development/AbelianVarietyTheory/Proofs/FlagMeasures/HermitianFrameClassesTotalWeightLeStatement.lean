import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermitianFrameClassesTotalWeightLe.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.hermitianFrameClasses_total_weight_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
