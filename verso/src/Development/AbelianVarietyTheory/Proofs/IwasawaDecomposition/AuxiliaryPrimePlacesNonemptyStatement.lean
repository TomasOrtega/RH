import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PdPlace.pD_nonempty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAuxiliaryPrimePlacesNonempty.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.auxiliaryPrimePlaces_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  first | exact @GlobalTheory.PdPlace.pD_nonempty | exact GlobalTheory.PdPlace.pD_nonempty | (intros; apply GlobalTheory.PdPlace.pD_nonempty <;> assumption)
