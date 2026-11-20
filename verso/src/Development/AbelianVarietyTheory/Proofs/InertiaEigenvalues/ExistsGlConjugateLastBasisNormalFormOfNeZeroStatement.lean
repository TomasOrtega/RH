import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsGlConjugateLastBasisNormalFormOfNeZero.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  first | exact @GlobalTheory.JR.Step.glNormal_of_ne_zero | exact GlobalTheory.JR.Step.glNormal_of_ne_zero | (intros; apply GlobalTheory.JR.Step.glNormal_of_ne_zero <;> assumption)
