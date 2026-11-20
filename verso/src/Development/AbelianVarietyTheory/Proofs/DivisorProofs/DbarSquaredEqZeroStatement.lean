import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSquaredEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.FlatAcyc.dbarF_dbarF` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDbarSquaredEqZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.dbar_squared_eq_zero : ∀ {g : ℕ} (f : (Fin g → ℂ) → Ext (0 + 0 + g))
    (hf1 : ∀ v, Differentiable ℝ (fun z => d01 f z v))
    (hsym : ∀ z v w, d01 (fun z' => d01 f z' v) z w = d01 (fun z' => d01 f z' w) z v)
    (z : Fin g → ℂ), dbarF (dbarF f) z = 0 := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.dbarF_dbarF | exact GlobalTheory.TorsionForm.FlatAcyc.dbarF_dbarF | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.dbarF_dbarF <;> assumption)
