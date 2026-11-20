import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.haar_UJ_isMulRightInvariant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIndefiniteUnitaryGroupHaarIsMulRightInvariant.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.haar_UJ_isMulRightInvariant | exact GlobalTheory.haar_UJ_isMulRightInvariant | (intros; apply GlobalTheory.haar_UJ_isMulRightInvariant <;> assumption)
