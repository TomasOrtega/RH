import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRankAtStalkOfConstFibreDim
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveRankAtStalkOfConstFibreDim.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) → Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  first | exact @GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | exact GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim | (intros; apply GlobalTheory.ConstFibreFree.projective_and_rankAtStalk_of_fibreDim <;> assumption)
