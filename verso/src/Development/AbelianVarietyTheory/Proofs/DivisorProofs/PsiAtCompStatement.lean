import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPsiAtComp.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.twAdm' : TwAdm := by
  first | exact @GlobalTheory.BigOn.Exp.twAdm | exact GlobalTheory.BigOn.Exp.twAdm | (intros; apply GlobalTheory.BigOn.Exp.twAdm <;> assumption)
