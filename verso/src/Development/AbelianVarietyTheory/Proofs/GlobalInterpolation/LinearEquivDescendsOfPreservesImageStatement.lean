import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImage
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLinearEquivDescendsOfPreservesImage.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
