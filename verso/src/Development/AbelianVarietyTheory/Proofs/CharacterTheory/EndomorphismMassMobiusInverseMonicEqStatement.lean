import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEq
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FEndomorphismMassMobiusInverseMonicEq.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  first | exact @GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div | exact GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div | (intros; apply GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div <;> assumption)
