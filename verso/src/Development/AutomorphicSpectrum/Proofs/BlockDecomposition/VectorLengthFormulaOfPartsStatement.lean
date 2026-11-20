import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FVectorLengthFormulaOfParts.lean&line=206#L206)
-/
theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
