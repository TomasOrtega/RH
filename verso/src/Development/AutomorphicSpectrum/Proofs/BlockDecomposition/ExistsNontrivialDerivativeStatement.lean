import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsNontrivialDerivative.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.exists_nontrivial_derivative : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | exact GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial <;> assumption)
