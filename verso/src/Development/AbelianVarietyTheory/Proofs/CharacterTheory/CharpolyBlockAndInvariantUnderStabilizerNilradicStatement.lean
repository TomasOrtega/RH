import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.charpoly_block` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FCharpolyBlockAndInvariantUnderStabilizerNilradic.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) * LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧ ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  first | exact @GlobalTheory.CuspGL.charpoly_block | exact GlobalTheory.CuspGL.charpoly_block | (intros; apply GlobalTheory.CuspGL.charpoly_block <;> assumption)
