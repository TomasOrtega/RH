import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchimedeanUnipotentTimesGLrSetClosedSubgroup.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ), (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧ (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  first | exact @GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | exact GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | (intros; apply GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup; all_goals assumption)
