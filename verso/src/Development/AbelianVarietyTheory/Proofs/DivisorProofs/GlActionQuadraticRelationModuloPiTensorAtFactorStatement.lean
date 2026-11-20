import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGlActionQuadraticRelationModuloPiTensorAtFactor.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  first | exact @GlobalTheory.HoweR.quadMod_actAt | exact GlobalTheory.HoweR.quadMod_actAt | (intros; apply GlobalTheory.HoweR.quadMod_actAt <;> assumption)
