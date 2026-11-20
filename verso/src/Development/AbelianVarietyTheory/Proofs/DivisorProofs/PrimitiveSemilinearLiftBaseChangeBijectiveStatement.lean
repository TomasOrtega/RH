import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveSemilinearLiftBaseChangeBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimitiveSemilinearLiftBaseChangeBijective.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.primitive_semilinearLift_baseChange_bijective : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R'], Module.Projective R (Cot R (CartierDual R A)) → Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by
  first | exact @GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective | exact GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective | (intros; apply GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective <;> assumption)
