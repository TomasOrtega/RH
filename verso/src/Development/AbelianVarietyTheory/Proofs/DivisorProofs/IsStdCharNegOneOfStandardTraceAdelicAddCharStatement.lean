import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsStdCharNegOneOfStandardTraceAdelicAddChar.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  first | exact @GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | exact GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | (intros; apply GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd <;> assumption)
