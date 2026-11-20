import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDimensionalArchimedeanSchwartzFockOperator.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_archimedeanSchwartzFockOperatorSpan : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  first | exact @GlobalTheory.FockKFinStep.dStep_finiteDimensional | exact GlobalTheory.FockKFinStep.dStep_finiteDimensional | (intros; apply GlobalTheory.FockKFinStep.dStep_finiteDimensional <;> assumption)
