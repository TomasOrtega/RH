import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNeg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuadSignLocal.quadSign_split_inert` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnramifiedQuadraticCharSignSplitEqOneInertEqNeg.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.unramifiedQuadraticCharSign_split_eq_one_inert_eq_neg : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → quadSign D v = 1) ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) := by
  first | exact @GlobalTheory.QuadSignLocal.quadSign_split_inert | exact GlobalTheory.QuadSignLocal.quadSign_split_inert | (intros; apply GlobalTheory.QuadSignLocal.quadSign_split_inert <;> assumption)
