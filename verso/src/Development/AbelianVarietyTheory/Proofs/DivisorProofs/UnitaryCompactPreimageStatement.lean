import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactPreimage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryCompactPreimage.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.unitary_compact_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (Matrix (Fin n) (Fin n) (AE F E))), IsCompact C → IsCompact {g : UA σ J | mat g ∈ C ∧ mat g⁻¹ ∈ C} := by
  first | exact @GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem | exact GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem | (intros; apply GlobalTheory.ThK.UnipDom.isCompact_setOf_mat_mem <;> assumption)
