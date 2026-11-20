import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormula
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAdelicDegreeFormula.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.adelic_degree_formula : MulF → MulI → LogAbsBasic → FinSupp → DegAdelic := by
  first | exact @GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | exact GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of | (intros; apply GlobalTheory.CompanionTheory.DegAdelicProof.degAdelic_of <;> assumption)
