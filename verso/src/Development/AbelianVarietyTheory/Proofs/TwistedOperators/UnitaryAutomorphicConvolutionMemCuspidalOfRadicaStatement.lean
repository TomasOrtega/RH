import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAutomorphicConvolutionMemCuspidalOfRadica
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryAutomorphicConvolutionMemCuspidalOfRadica.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ := by
  first | exact @GlobalTheory.RopCusp.ropG_mem_L2cusp | exact GlobalTheory.RopCusp.ropG_mem_L2cusp | (intros; apply GlobalTheory.RopCusp.ropG_mem_L2cusp <;> assumption)
