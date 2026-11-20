import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryCharacterFacts.lean&line=288#L288)
-/
theorem _root_.GlobalTheory.T.unitary_character_facts : PositivityTheory.SphericalProduct.CharU := by
  first | exact @GlobalTheory.CompanionTheory.TorusChar.charU | exact GlobalTheory.CompanionTheory.TorusChar.charU | (intros; apply GlobalTheory.CompanionTheory.TorusChar.charU <;> assumption)
