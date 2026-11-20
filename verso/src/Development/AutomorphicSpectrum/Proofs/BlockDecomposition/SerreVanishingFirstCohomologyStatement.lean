import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSerreVanishingFirstCohomology.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.serre_vanishing_first_cohomology : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one | exact GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one | (intros; apply GlobalTheory.CompanionTheory.GE.Step.serre_vanishing_coh_one <;> assumption)
