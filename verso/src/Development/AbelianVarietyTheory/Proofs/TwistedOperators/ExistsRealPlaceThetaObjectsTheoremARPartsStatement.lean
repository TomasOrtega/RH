import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARParts
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealPlaceTheta.exists_record_theta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsRealPlaceThetaObjectsTheoremARParts.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧ DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta | exact GlobalTheory.RealPlaceTheta.exists_record_theta | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta <;> assumption)
