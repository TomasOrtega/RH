import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteIndicatorSmulArchFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralFiniteIndicatorSmulArchFunction.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.integral_finiteIndicator_smul_archFunction : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  first | exact @GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | exact GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch | (intros; apply GlobalTheory.TrProdInt.integral_indicatorFin_smul_arch <;> assumption)
