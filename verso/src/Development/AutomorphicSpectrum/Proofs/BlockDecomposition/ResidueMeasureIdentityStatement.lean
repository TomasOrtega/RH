import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FResidueMeasureIdentity.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.residue_measure_identity : MapsExist → HtExist → HeckeEta → FJEis → PcBound → RSec → EisHol → ThTotal → PcFc → SphBound → PositivityTheory.PfSWUS.FourierZero → PositivityTheory.PfSWUS.CoefDataExists → ResMu := by
  first | exact @GlobalTheory.CompanionTheory.ResMu.resMu_main | exact GlobalTheory.CompanionTheory.ResMu.resMu_main | (intros; apply GlobalTheory.CompanionTheory.ResMu.resMu_main <;> assumption)
