import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheaf
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAmpleTwistSectionsGenerateSubsheaf.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.ample_twist_sections_generate_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P, (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le | exact GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le <;> assumption)
