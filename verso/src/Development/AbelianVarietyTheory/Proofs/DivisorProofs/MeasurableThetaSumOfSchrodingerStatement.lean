import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaTransformMeas.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeasurableThetaSumOfSchrodinger.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.measurable_theta_sum_of_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  first | exact @GlobalTheory.ThetaTransformMeas.main | exact GlobalTheory.ThetaTransformMeas.main | (intros; apply GlobalTheory.ThetaTransformMeas.main <;> assumption)
