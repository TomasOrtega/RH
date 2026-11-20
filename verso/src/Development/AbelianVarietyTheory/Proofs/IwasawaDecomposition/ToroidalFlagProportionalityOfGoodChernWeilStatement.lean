import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FToroidalFlagProportionalityOfGoodChernWeil.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality := by
  first | exact @GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | exact GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | (intros; apply GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil <;> assumption)
