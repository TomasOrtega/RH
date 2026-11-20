import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.KerAevalAddStabilizerNilradicalSocle
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.ker_aeval_add_nilRad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FKerAevalAddStabilizerNilradicalSocle.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  first | exact @GlobalTheory.CuspGL.ker_aeval_add_nilRad | exact GlobalTheory.CuspGL.ker_aeval_add_nilRad | (intros; apply GlobalTheory.CuspGL.ker_aeval_add_nilRad <;> assumption)
