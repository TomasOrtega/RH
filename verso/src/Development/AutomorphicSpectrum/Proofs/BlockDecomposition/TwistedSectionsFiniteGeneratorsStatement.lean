import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGenerators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedSectionsFiniteGenerators.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.twisted_sections_finite_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | exact GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | (intros; apply GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit <;> assumption)
