import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D10ProductRuleSymmetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq.dbarAdjF_dbarAdjF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FD10ProductRuleSymmetric.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.dbarAdjF_dbarAdjF_eq_zero_of_d10_symm : ∀ {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ)
    (hf1 : ∀ v, Differentiable ℝ (fun z => d10 f z v)) (hψ1 : ∀ v, Differentiable ℝ (fun z => d10 ψ z v))
    (hsf : ∀ z v w, d10 (fun z' => d10 f z' v) z w = d10 (fun z' => d10 f z' w) z v)
    (hsψ : ∀ z v w, d10 (fun z' => d10 ψ z' v) z w = d10 (fun z' => d10 ψ z' w) z v)
    (z : Fin g → ℂ), dbarAdjF G ψ (dbarAdjF G ψ f) z = 0 := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq.dbarAdjF_dbarAdjF | exact GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq.dbarAdjF_dbarAdjF | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.DbarAdjSq.dbarAdjF_dbarAdjF <;> assumption)
