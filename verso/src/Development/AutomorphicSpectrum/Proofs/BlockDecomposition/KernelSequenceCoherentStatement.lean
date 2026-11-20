import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherent
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelSequenceCoherent.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.kernel_sequence_coherent : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, IsCoherent (KerSeq.kerSeq T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq | exact GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq | (intros; apply GlobalTheory.CompanionTheory.GE.isCoherent_kerSeq <;> assumption)
