import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOfAlgebraicModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralModelOfAlgebraicModel.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.integral_model_of_algebraic_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  first | exact @GlobalTheory.LatModel.modelInt | exact GlobalTheory.LatModel.modelInt | (intros; apply GlobalTheory.LatModel.modelInt <;> assumption)
