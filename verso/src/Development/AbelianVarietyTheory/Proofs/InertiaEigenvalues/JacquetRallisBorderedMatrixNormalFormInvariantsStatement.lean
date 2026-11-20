import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisBorderedMatrixNormalFormInvariants.lean&line=233#L233)
-/
theorem _root_.GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  first | exact @GlobalTheory.JR.normalForm_invariants | exact GlobalTheory.JR.normalForm_invariants | (intros; apply GlobalTheory.JR.normalForm_invariants <;> assumption)
