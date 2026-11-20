import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.Step.lifts_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLiftingBaseOfVanishingCohomology.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.lifting_base_of_vanishing_cohomology : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ), Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_zero | exact GlobalTheory.CompanionTheory.GE.Step.lifts_zero | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_zero <;> assumption)
