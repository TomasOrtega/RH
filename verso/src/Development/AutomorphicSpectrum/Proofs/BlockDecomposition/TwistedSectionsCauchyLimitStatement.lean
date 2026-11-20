import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.exists_limit_twPow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedSectionsCauchyLimit.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.twisted_sections_cauchy_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_limit_twPow | exact GlobalTheory.CompanionTheory.GE.exists_limit_twPow | (intros; apply GlobalTheory.CompanionTheory.GE.exists_limit_twPow <;> assumption)
