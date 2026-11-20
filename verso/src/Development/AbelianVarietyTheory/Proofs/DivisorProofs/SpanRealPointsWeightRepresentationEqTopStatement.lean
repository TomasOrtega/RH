import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRealPointsWeightRepresentationEqTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpanRealPointsWeightRepresentationEqTop.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.span_realPoints_weightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | exact GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | (intros; apply GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU <;> assumption)
