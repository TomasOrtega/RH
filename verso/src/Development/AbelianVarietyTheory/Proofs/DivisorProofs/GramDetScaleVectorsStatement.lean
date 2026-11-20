import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetScaleVectors
import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGramDetScaleVectors.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.gram_det_scale_vectors : ∀ {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) (d : Fin n → K), (h.gram σ (fun j => d j • v j)).det.re = (∏ j, ‖σ (d j)‖ ^ 2) * (h.gram σ v).det.re := by
  first | exact @GlobalTheory.hermFam_gram_det_re_smul | exact GlobalTheory.hermFam_gram_det_re_smul | (intros; apply GlobalTheory.hermFam_gram_det_re_smul <;> assumption)
