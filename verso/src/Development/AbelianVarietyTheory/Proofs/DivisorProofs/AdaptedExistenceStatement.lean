import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.adaptEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdaptedExistence.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.adapted_existence : AdaptEx := by
  first | exact @GlobalTheory.BigOn.Exp.adaptEx | exact GlobalTheory.BigOn.Exp.adaptEx | (intros; apply GlobalTheory.BigOn.Exp.adaptEx <;> assumption)
