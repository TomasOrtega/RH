import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOfIsCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightBound.height_le_of_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeightLeOfIsCompact.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.height_bounded_of_toL_mem_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := by
  first | exact @GlobalTheory.HeightBound.height_le_of_isCompact | exact GlobalTheory.HeightBound.height_le_of_isCompact | (intros; apply GlobalTheory.HeightBound.height_le_of_isCompact <;> assumption)
