import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSup
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.generated_subsheaf_add_le_sup : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)), genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le <;> assumption)
