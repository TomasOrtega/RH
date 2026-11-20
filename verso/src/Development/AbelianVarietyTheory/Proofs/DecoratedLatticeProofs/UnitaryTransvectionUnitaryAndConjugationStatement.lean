import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TransvAdelic.transv_unitary_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnitaryTransvectionUnitaryAndConjugation.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.unitaryTransvection_unitary_and_conjugation : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  first | exact @GlobalTheory.TransvAdelic.transv_unitary_conj | exact GlobalTheory.TransvAdelic.transv_unitary_conj | (intros; apply GlobalTheory.TransvAdelic.transv_unitary_conj <;> assumption)
