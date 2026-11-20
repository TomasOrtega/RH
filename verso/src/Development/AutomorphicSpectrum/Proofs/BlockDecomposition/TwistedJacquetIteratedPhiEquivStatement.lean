import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedJacquetIteratedPhiEquiv.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.twisted_jacquet_iterated_phi_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)), Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ] TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv <;> assumption)
