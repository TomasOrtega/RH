import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfUnit.exists_int_inv_half` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIntegralInverseOnConjugateHalf.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.exists_integral_inverse_on_conjugate_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) → ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  first | exact @GlobalTheory.HalfUnit.exists_int_inv_half | exact GlobalTheory.HalfUnit.exists_int_inv_half | (intros; apply GlobalTheory.HalfUnit.exists_int_inv_half <;> assumption)
