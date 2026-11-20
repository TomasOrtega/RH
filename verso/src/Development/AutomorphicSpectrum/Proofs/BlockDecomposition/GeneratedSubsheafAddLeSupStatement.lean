import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSup
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGeneratedSubsheafAddLeSup.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.generated_subsheaf_add_le_sup : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)), genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le <;> assumption)
