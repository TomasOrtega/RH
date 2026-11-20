import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPower
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGeneratedSubsheafLeIdealPower.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.generated_subsheaf_le_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)), c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub <;> assumption)
