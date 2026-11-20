import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedClosedSystemCoherent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGradedClosedSystemCoherent.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.graded_closed_system_coherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] {P : X.Modules}, IsCoherent P → ∀ (S : ℕ → Subobject P) (hS : ClosedSys I P S) (e : ℕ), IsCoherent (gr (anti hS) e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | exact GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr | (intros; apply GlobalTheory.CompanionTheory.GE.Step.isCoherent_gr <;> assumption)
