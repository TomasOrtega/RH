import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduci
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.psi_of_irreducible_charpoly` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FInvariantSubspaceMobiusInverseCharpolyOfIrreduci.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  first | exact @GlobalTheory.CuspGL.psi_of_irreducible_charpoly | exact GlobalTheory.CuspGL.psi_of_irreducible_charpoly | (intros; apply GlobalTheory.CuspGL.psi_of_irreducible_charpoly <;> assumption)
