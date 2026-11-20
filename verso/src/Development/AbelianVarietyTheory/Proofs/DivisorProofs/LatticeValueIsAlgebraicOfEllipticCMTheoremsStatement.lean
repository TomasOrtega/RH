import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeValueIsAlgebraicOfEllipticCMTheorems.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  first | exact @GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | exact GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | (intros; apply GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen <;> assumption)
