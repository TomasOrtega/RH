import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Introduce `D c 𝒯 t L`. Establish `hTwo : TwoX t` using `GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D) L.com L.tup L.real L.ker L.rd`. Establish `hRap : RapidVal D` using `GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D`. Establish `hStep : StepX t` using `GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo …`. Establish `hLast : LastX t` using `GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd`.

Conclude with `GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast`.
-/
theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
