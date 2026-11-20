import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTypeHypothesisFormsAgree.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.typeHypothesis_forms_agree : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  first | exact @GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | exact GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | (intros; apply GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed <;> assumption)
