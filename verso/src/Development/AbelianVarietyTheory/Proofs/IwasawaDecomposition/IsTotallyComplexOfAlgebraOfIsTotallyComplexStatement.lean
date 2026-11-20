import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplex
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isTotallyComplex_of_algebra` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsTotallyComplexOfAlgebraOfIsTotallyComplex.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K := by
  first | exact @GlobalTheory.isTotallyComplex_of_algebra | exact GlobalTheory.isTotallyComplex_of_algebra | (intros; apply GlobalTheory.isTotallyComplex_of_algebra <;> assumption)
