import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsOpenAdditiveCharacterKernel.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
