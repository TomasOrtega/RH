import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwist
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FEigenspaceFrobeniusTwist.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.eigenspace_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | exact GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist <;> assumption)
