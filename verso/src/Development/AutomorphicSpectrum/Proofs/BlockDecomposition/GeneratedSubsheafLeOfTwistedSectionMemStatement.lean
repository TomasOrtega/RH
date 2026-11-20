import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.TwGen.genSub_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGeneratedSubsheafLeOfTwistedSectionMem.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_le <;> assumption)
