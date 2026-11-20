import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FConjugatePlacesFacts.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.conjugate_places_facts : ConjPlaces := by
  first | exact @GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | exact GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | (intros; apply GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces <;> assumption)
