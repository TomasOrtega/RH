import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanIwasawaDecomposition
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
Apply `GlobalTheory.IwArchMin.iwasawa_minPar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FArchimedeanIwasawaDecomposition.lean&line=216#L216)
-/
theorem _root_.GlobalTheory.T.archimedean_iwasawa_decomposition : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ w (g : GArch D.sp.cm.sig V.gram w), ∃ p ∈ PArch Φ.flag0 w, ∃ k ∈ stabArch D.sp.cm.sig V.gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a), g = p * k := by
  first | exact @GlobalTheory.IwArchMin.iwasawa_minPar | exact GlobalTheory.IwArchMin.iwasawa_minPar | (intros; apply GlobalTheory.IwArchMin.iwasawa_minPar <;> assumption)
