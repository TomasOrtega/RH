import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.SeparableIntegralModelAlmostAll
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodPlaces.goodPlaces` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FAutomorphicKernels%2FIsobaricBaseChange%2FIntegralCoefficientBaseChange%2FUnitaryBaseChangeCharacters%2FUnitaryBaseChangeLinks%2FSeparableIntegralModelAlmostAll.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.separable_integral_model_almost_all : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable → ∀ᶠ w in (cofinite : Filter (Pl E)), ∃ Q₀ : (intL (w.adicCompletion E))[X], Q₀.Separable ∧ Q₀.map (intL (w.adicCompletion E)).subtype = P.map (algebraMap E (w.adicCompletion E)) := by
  first | exact @GlobalTheory.GoodPlaces.goodPlaces | exact GlobalTheory.GoodPlaces.goodPlaces | (intros; apply GlobalTheory.GoodPlaces.goodPlaces <;> assumption)
