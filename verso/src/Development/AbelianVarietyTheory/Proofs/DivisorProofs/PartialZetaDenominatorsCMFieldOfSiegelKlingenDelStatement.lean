import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators := by
  first | exact @GlobalTheory.ZetaDenom.zetaDenominators | exact GlobalTheory.ZetaDenom.zetaDenominators | (intros; apply GlobalTheory.ZetaDenom.zetaDenominators <;> assumption)
