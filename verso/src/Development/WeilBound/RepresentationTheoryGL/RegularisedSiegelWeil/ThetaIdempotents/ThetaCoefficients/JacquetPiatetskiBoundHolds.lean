import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
open GlobalTheory.CompanionTheory.Jp
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.jacquet_piatetski_bound_holds : GlobalTheory.CompanionTheory.Jp.GoodPlacesOutsideFiniteSet := by
  first | exact @PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | exact PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound | (intros; apply PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound <;> assumption)
