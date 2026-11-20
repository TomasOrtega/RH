import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRealisedOnAdelicSchwartzWeylFourier.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  first | exact @GlobalTheory.AdelicSvN.Weyl.realised_weyl | exact GlobalTheory.AdelicSvN.Weyl.realised_weyl | (intros; apply GlobalTheory.AdelicSvN.Weyl.realised_weyl <;> assumption)
