import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLiftingInductiveSuccessiveApproximation.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.lifting_inductive_successive_approximation : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ), Lifts I H hS n (e + 1) → ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | exact GlobalTheory.CompanionTheory.GE.Step.step_of_lifts | (intros; apply GlobalTheory.CompanionTheory.GE.Step.step_of_lifts <;> assumption)
