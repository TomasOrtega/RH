import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelOfDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LatJet.modelConj_of_deRham | exact GlobalTheory.LatJet.modelConj_of_deRham | (intros; apply GlobalTheory.LatJet.modelConj_of_deRham <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.conjugate_model_of_de_rham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelConj := by
  first | exact @GlobalTheory.LatJet.modelConj_of_deRham | exact GlobalTheory.LatJet.modelConj_of_deRham | (intros; apply GlobalTheory.LatJet.modelConj_of_deRham <;> assumption)
