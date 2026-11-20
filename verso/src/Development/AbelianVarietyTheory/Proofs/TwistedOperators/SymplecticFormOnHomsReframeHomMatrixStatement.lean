import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOnHomsReframeHomMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSymplecticFormOnHomsReframeHomMatrix.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.symplecticFormOnHoms_reframeHomMatrix : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := by
  first | exact @GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | exact GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW | (intros; apply GlobalTheory.AdSpan.ReVec.Sympl.symplO_reW <;> assumption)
