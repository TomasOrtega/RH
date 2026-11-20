import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroup
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FRatZariskiClosureOfAutStableSLGroup.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  first | exact @GlobalTheory.ClassFin.RatClosure.ratClosure | exact GlobalTheory.ClassFin.RatClosure.ratClosure | (intros; apply GlobalTheory.ClassFin.RatClosure.ratClosure <;> assumption)
