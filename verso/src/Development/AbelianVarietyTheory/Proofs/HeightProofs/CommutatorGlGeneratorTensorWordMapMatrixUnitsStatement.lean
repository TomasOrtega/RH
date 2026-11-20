import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnits
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothForms.commutator_wordMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FCommutatorGlGeneratorTensorWordMapMatrixUnits.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), E a b * wordMap E d M - wordMap E d M * E a b = wordMap E d (polar n d a b * M - M * polar n d a b) := by
  first | exact @GlobalTheory.SmoothForms.commutator_wordMap | exact GlobalTheory.SmoothForms.commutator_wordMap | (intros; apply GlobalTheory.SmoothForms.commutator_wordMap <;> assumption)
