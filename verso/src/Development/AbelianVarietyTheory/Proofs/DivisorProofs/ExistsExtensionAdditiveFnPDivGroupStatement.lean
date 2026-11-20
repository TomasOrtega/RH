import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsExtensionAdditiveFnPDivGroup.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.exists_extension_additive_fn_pDivGroup : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (b : G.A 1), cobOne R (G.A 1) b = 0 → ∃ B : G.funs, B.1 1 = b ∧ ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  first | exact @GlobalTheory.PDivGroup.exists_funs_transl_eq_add | exact GlobalTheory.PDivGroup.exists_funs_transl_eq_add | (intros; apply GlobalTheory.PDivGroup.exists_funs_transl_eq_add <;> assumption)
