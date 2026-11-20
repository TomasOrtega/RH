import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuations
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRootsEqOfDistinctValuations.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.roots_eq_of_distinct_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) → ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  first | exact @GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | exact GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | (intros; apply GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord <;> assumption)
