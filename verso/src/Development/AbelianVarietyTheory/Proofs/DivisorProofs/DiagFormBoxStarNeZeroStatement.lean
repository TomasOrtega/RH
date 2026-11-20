import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiagSq.lDiag_boxFun_star_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDiagFormBoxStarNeZero.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.diag_form_box_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ → AF F) → ℂ),
    φ ∈ schA F κ → φ ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun φ (star φ)) ≠ 0 := by
  first | exact @GlobalTheory.DiagSq.lDiag_boxFun_star_ne | exact GlobalTheory.DiagSq.lDiag_boxFun_star_ne | (intros; apply GlobalTheory.DiagSq.lDiag_boxFun_star_ne <;> assumption)
