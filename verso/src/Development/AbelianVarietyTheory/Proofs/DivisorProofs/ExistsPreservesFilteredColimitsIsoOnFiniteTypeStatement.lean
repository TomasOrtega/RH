import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteType
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso`. Consider the case `exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso`. Consider the case `(intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
