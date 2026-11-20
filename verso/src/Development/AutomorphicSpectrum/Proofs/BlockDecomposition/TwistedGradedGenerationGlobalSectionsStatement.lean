import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedGradedGenerationGlobalSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedGradedGenerationGlobalSections.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.twisted_graded_generation_global_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {P : X.Modules} (S : ℕ → Subobject P) (hS : ClosedSys I P S) {k : ℕ} (g : Fin k → A), (∀ i, g i ∈ I) → ∀ (hr : ∀ i, MapsDown S (toFunctions (X := X) (A := A) ⊤ (g i))) (n : ℤ) (e : ℕ), Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grT (anti hS) (hr i) e)).app ⊤)) = ⊤ → Lifts I H hS n e → Lifts I H hS n (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.lifts_succ | exact GlobalTheory.CompanionTheory.GE.Step.lifts_succ | (intros; apply GlobalTheory.CompanionTheory.GE.Step.lifts_succ <;> assumption)
