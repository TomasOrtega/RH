import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicSvNQuad.realised_unip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowerUnipotentRealisedOnAdelicSchwartz.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  first | exact @GlobalTheory.AdelicSvNQuad.realised_unip | exact GlobalTheory.AdelicSvNQuad.realised_unip | (intros; apply GlobalTheory.AdelicSvNQuad.realised_unip <;> assumption)
