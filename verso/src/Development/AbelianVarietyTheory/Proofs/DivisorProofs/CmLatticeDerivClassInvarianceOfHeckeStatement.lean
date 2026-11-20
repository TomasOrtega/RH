import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
