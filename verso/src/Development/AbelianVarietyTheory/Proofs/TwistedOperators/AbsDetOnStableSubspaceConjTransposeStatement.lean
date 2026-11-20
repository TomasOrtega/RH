import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceConjTranspose
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAbsDetOnStableSubspaceConjTranspose.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.absDetOnStableSubspace_conjTranspose : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, g *ᵥ y ∈ V) → (∀ y ∈ V, gᴴ *ᵥ y ∈ V) → GlobalTheory.FlagMeas.detOn gᴴ V = GlobalTheory.FlagMeas.detOn g V := by
  first | exact @GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | exact GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose | (intros; apply GlobalTheory.FlagMeas.DetAdj.detOn_conjTranspose <;> assumption)
