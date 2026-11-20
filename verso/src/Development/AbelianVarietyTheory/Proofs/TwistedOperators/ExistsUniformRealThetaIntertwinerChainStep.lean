import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPosStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeriesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.Published GlobalTheory.Chain.RealIt

namespace GlobalTheory.Chain.ItPairObj

/- English proof (translation)
Take `⟨X, hX⟩` from `GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)`. Establish `a1 : admH1 X` using `GlobalTheory.FockDeg.degrees_and_adjoints X`. Establish `a2 : admH2 X` using `GlobalTheory.JointHarm.fock_polynomials X`. Establish `a3 : DiscreteSeriesBlattner X` using `GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX`. Establish `a5 : admQ5 X` using `hH.admQ5_of_harishChandraModules X`.

Establish `a6 : CoverHaarIntegration X` using `GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X`. Establish `a7 : admQ7` using `GlobalTheory.TensorHW.highestWeight_tensor`. Establish `a8 : admQ8` using `GlobalTheory.InducedPBW.pbw_induced`. Establish `a4 : DiscreteSeriesPositivity X` using `GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8`. Establish `h1` using `GlobalTheory.T.doublingIntegral_jointHarmonic_pos X a1 a2 a3 a4 a5 a6 a7 a8`.

Conclude with `⟨X, hX, h1, GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩`.
-/
theorem exists_record (hD : DiscreteSeriesCover) (hH : HarishChandraModules) :
    ∃ X : ProvA, ChosenSeries X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X := by
  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam (GlobalTheory.CoverDS.exists_hasParam hD)
  have a1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have a2 : admH2 X := GlobalTheory.JointHarm.fock_polynomials X
  have a3 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hD X hX
  have a5 : admQ5 X := hH.admQ5_of_harishChandraModules X
  have a6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have a7 : admQ7 := GlobalTheory.TensorHW.highestWeight_tensor
  have a8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have a4 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X a3 a5 a7 a8
  have h1 := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨X, hX, h1, GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X a1 a2 a3 a4 a5 a6 a7 a8 h1⟩

/- English proof (translation)
Take `⟨X, hX, h1, h2⟩` from `exists_record hD hH`. Conclude with `itPair D X hX h1 h2 hF hV hB hC`.
-/
theorem itPair_of_rows (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D) (hV : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (hC : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction) : ItPair D := by
  obtain ⟨X, hX, h1, h2⟩ := exists_record hD hH
  exact itPair D X hX h1 h2 hF hV hB hC

/- English proof (translation)
The claim follows from `itPair_of_rows hD hH D (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D) (GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D) (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) GlobalTheory.Contr.contraction`.
-/
theorem itPair_holds (hD : DiscreteSeriesCover) (hH : HarishChandraModules) (D : D7) : ItPair D :=
  itPair_of_rows hD hH D (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D) (GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D) (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) GlobalTheory.Contr.contraction

end GlobalTheory.Chain.ItPairObj
