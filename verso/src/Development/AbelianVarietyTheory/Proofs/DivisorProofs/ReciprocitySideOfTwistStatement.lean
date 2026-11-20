import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideOfTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.recSide_of_twAdm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReciprocitySideOfTwist.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.reciprocity_side_of_twist : TwAdm → RecSide := by
  first | exact @GlobalTheory.BigOn.Exp.recSide_of_twAdm | exact GlobalTheory.BigOn.Exp.recSide_of_twAdm | (intros; apply GlobalTheory.BigOn.Exp.recSide_of_twAdm <;> assumption)
