import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionCancelOfOne
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FMonicFactorizationConvolutionCancelOfOne.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.monicFactorizationConvolution_cancel_of_one : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 → (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  first | exact @GlobalTheory.CuspGL.ConvCancel.conv_cancel | exact GlobalTheory.CuspGL.ConvCancel.conv_cancel | (intros; apply GlobalTheory.CuspGL.ConvCancel.conv_cancel <;> assumption)
