import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetZetaOfDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJetZetaOfDeRham.lean&line=189#L189)
-/
theorem _root_.GlobalTheory.T.jet_zeta_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  first | exact @GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | exact GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta | (intros; apply GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta <;> assumption)
