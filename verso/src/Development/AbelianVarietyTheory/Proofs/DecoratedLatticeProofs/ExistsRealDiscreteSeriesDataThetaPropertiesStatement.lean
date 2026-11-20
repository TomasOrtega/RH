import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealPlaceTheta.exists_record_theta_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsRealDiscreteSeriesDataThetaProperties.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_real_discreteSeries_data_theta_properties : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta_all | exact GlobalTheory.RealPlaceTheta.exists_record_theta_all | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta_all <;> assumption)
