import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDerivativeZeroWhittakerKernel.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.derivative_zero_whittaker_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | exact GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero | (intros; apply GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero <;> assumption)
