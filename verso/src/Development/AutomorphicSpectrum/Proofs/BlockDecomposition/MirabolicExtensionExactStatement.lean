import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicExtensionExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMirabolicExtensionExact.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.mirabolic_extension_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A B C : MRep k n), MExt A B C → Ses A.ρ B.ρ C.ρ := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | exact GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.ses_of_mext <;> assumption)
