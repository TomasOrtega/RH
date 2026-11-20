import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceTopIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFormalExistenceTopIdeal.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.formal_existence_top_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))], Statement I (⊤ : X.IdealSheafData) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Unit.statement_top | exact GlobalTheory.CompanionTheory.GE.Unit.statement_top | (intros; apply GlobalTheory.CompanionTheory.GE.Unit.statement_top <;> assumption)
