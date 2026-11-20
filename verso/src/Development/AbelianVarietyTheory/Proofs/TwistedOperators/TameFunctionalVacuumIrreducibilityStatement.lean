import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Irr.irr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTameFunctionalVacuumIrreducibility.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.tame_functional_vacuum_irreducibility : ∀ D : D7, Irr D := by
  first | exact @GlobalTheory.Irr.irr | exact GlobalTheory.Irr.irr | (intros; apply GlobalTheory.Irr.irr <;> assumption)
