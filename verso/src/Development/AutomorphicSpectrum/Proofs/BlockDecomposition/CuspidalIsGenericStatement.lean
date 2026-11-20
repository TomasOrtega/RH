import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalIsGeneric.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.cuspidal_is_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  first | exact @GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal <;> assumption)
