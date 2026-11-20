import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmallerSource.no_map_smaller_source` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNoIntertwinerSmallerFockToDiscreteSeries.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.SmallerSource.no_map_smaller_source | exact GlobalTheory.SmallerSource.no_map_smaller_source | (intros; apply GlobalTheory.SmallerSource.no_map_smaller_source <;> assumption)
