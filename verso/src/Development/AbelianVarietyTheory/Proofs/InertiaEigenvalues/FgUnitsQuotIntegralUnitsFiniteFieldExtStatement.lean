import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgUnitsQuotIntegralUnitsFiniteFieldExt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldUnitsQuotFG.fg_units_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFgUnitsQuotIntegralUnitsFiniteFieldExt.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  first | exact @GlobalTheory.FieldUnitsQuotFG.fg_units_quot | exact GlobalTheory.FieldUnitsQuotFG.fg_units_quot | (intros; apply GlobalTheory.FieldUnitsQuotFG.fg_units_quot <;> assumption)
