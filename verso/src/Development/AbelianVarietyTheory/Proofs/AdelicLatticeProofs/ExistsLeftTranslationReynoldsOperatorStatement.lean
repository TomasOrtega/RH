import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperator
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsLeftTranslationReynoldsOperator.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.exists_leftTranslation_reynoldsOperator : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  first | exact @GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds | exact GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds | (intros; apply GlobalTheory.ClassFin.ReynoldsLtr.exists_isReynolds <;> assumption)
