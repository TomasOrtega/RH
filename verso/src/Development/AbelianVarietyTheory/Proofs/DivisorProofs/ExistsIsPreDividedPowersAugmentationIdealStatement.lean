import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsPreDividedPowersAugmentationIdeal.lean&line=318#L318)
-/
theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧ ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | exact GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation <;> assumption)
