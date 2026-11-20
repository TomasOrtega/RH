import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsSplitPlaceOfIsSplitPlaceCmField.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_splitPlace_of_isSplitPlace_cmField : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P → ∃ s : SplitPlace D.host.E, s.w = P := by
  first | exact @GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace | exact GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace | (intros; apply GlobalTheory.HeightCounting.SplitPlaceOf.exists_splitPlace <;> assumption)
