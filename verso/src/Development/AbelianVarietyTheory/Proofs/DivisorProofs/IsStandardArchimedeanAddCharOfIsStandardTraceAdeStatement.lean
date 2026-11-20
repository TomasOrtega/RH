import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsStandardArchimedeanAddCharOfIsStandardTraceAde.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | exact GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | (intros; apply GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd <;> assumption)
