import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwistChr.twChr_of_twAdm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistCharacterOfArtin.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.twist_character_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → TwAdm → TwChr := by
  first | exact @GlobalTheory.TwistChr.twChr_of_twAdm | exact GlobalTheory.TwistChr.twChr_of_twAdm | (intros; apply GlobalTheory.TwistChr.twChr_of_twAdm <;> assumption)
