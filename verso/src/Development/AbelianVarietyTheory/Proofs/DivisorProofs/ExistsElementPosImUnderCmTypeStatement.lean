import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMTypeImPos.exists_im_pos` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsElementPosImUnderCmType.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_element_pos_im_under_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
