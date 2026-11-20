import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantVanishingAtZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetEqv.vanishAt_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantVanishingAtZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.determinant_vanishing_at_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.DetEqv.VanishAt k 0 := by
  first | exact @GlobalTheory.DetEqv.vanishAt_zero | exact GlobalTheory.DetEqv.vanishAt_zero | (intros; apply GlobalTheory.DetEqv.vanishAt_zero <;> assumption)
