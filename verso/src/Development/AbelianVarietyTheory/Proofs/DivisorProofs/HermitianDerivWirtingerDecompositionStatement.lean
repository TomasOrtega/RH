import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDerivWirtingerDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianDerivWirtingerDecomposition.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.hermitian_deriv_wirtinger_decomposition : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ} (H : E → Matrix (Fin m) (Fin m) ℂ) (w : E), (∀ᶠ w' in 𝓝 w, (H w').IsHermitian) → (∀ a b, DifferentiableAt ℝ (fun w' => H w' a b) w) → ∀ ξ : E, dMat H w ξ = wirt H w ξ + (wirt H w ξ)ᴴ := by
  first | exact @GlobalTheory.MatDeriv.dMat_eq_wirt_add_conjTranspose_wirt | exact GlobalTheory.MatDeriv.dMat_eq_wirt_add_conjTranspose_wirt | (intros; apply GlobalTheory.MatDeriv.dMat_eq_wirt_add_conjTranspose_wirt <;> assumption)
