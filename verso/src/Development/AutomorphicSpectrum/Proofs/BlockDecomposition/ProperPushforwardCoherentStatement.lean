import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProperPushforwardCoherent.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.proper_pushforward_coherent : ∀ {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → ∀ {G : Z.Modules}, IsCoherent G → IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | exact GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper <;> assumption)
