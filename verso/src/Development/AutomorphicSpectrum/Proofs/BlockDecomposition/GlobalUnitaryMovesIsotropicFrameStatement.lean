import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrame
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGlobalUnitaryMovesIsotropicFrame.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.global_unitary_moves_isotropic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 <;> assumption)
