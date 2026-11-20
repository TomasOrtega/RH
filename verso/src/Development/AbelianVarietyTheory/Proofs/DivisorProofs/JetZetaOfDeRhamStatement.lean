import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetZetaOfDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | exact GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | (intros; apply GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.jet_zeta_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  first | exact @GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | exact GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | (intros; apply GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta <;> assumption)
