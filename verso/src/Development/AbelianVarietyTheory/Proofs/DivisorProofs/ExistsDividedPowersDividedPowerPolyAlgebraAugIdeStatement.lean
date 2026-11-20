import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDA.exists_dividedPowers_aug` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDividedPowersDividedPowerPolyAlgebraAugIde.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_aug | exact GlobalTheory.PDA.exists_dividedPowers_aug | (intros; apply GlobalTheory.PDA.exists_dividedPowers_aug <;> assumption)
