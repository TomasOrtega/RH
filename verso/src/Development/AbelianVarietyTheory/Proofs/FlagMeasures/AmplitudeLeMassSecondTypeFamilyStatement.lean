import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplitudeLeMassSecondTypeFamily.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.amplitude_le_mass_secondType_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (β J βJ : ℕ) (d : S.Datum), ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤ ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  first | exact @GlobalTheory.HL.AmpCancel.amp_le_mass | exact GlobalTheory.HL.AmpCancel.amp_le_mass | (intros; apply GlobalTheory.HL.AmpCancel.amp_le_mass <;> assumption)
