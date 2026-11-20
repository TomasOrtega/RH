import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMultilinearFormOfPicTorsion.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.exists_multilinear_form_of_pic_torsion : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap B (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  first | exact @GlobalTheory.PicTorsionForm.exists_form | exact GlobalTheory.PicTorsionForm.exists_form | (intros; apply GlobalTheory.PicTorsionForm.exists_form <;> assumption)
