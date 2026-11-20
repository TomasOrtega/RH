import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWhittakerSpaceDimFiniteGLLeOne.lean&line=399#L399)
-/
theorem _root_.GlobalTheory.T.whittakerSpaceDimFiniteGL_le_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V), τ.IsIrreducible → whDim ψ τ ≤ 1 := by
  first | exact @GlobalTheory.FinGL.GGFree.whDim_le_one | exact GlobalTheory.FinGL.GGFree.whDim_le_one | (intros; apply GlobalTheory.FinGL.GGFree.whDim_le_one <;> assumption)
