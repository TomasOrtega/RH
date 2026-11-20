import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExponentialPolynomialSolutionSpaceFiniteDimensio.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l) := by
  first | exact @GlobalTheory.HCF.expSol_finiteDimensional | exact GlobalTheory.HCF.expSol_finiteDimensional | (intros; apply GlobalTheory.HCF.expSol_finiteDimensional <;> assumption)
