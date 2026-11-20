import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLe
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGL.finsum_psi_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FFinsumMobiusInverseCharpolyInvariantLe.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) = s (LinearMap.charpoly (g.restrict hg)) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_le | exact GlobalTheory.CuspGL.finsum_psi_le | (intros; apply GlobalTheory.CuspGL.finsum_psi_le <;> assumption)
