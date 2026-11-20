import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPsiPreservesIsomorphism.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.psi_preserves_isomorphism : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | exact GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.PsiIso.giso_psiN <;> assumption)
