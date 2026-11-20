import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedJacquetPhiMinusEquiv.lean&line=282#L282)
-/
theorem _root_.GlobalTheory.T.twisted_jacquet_phi_minus_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m n : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), Nonempty (TwJacquet (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n) ≃ₗ[ℂ] TwJacquet τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv <;> assumption)
