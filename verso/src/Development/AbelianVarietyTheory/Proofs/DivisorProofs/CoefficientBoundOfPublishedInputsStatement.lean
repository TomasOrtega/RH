import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoefficientBoundOfHyp.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.coefficient_bound_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → BigC fun _ ch C _ => CoefAt ch C := by
  first | exact @GlobalTheory.ArchTens.VolSize.coefK | exact GlobalTheory.ArchTens.VolSize.coefK | (intros; apply GlobalTheory.ArchTens.VolSize.coefK <;> assumption)
