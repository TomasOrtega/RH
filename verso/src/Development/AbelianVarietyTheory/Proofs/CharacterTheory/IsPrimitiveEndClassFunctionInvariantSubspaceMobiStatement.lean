import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.isPrimitive_psi` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FIsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_psi | exact GlobalTheory.CuspGL.isPrimitive_psi | (intros; apply GlobalTheory.CuspGL.isPrimitive_psi <;> assumption)
