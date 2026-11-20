import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIteratedFDerivApplyEqFoldrDirectionalFderiv.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  first | exact @GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | exact GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | (intros; apply GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv <;> assumption)
