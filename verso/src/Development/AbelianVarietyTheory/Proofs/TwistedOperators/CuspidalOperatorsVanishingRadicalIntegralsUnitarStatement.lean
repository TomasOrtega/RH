import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitary
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspidalOpAssembly.cuspidalOperators` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCuspidalOperatorsVanishingRadicalIntegralsUnitary.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.cuspidalOperators_vanishingRadicalIntegrals_unitaryGroup : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CuspidalOperators V μ := by
  first | exact @GlobalTheory.CuspidalOpAssembly.cuspidalOperators | exact GlobalTheory.CuspidalOpAssembly.cuspidalOperators | (intros; apply GlobalTheory.CuspidalOpAssembly.cuspidalOperators <;> assumption)
