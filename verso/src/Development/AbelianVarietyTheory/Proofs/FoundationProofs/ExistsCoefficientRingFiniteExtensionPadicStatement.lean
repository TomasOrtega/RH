import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadic
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCoefficientRingFiniteExtensionPadic.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_coefficientRing_finiteExtension_padic : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E → ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CoefJoin.coef_of_finite | exact GlobalTheory.CoefJoin.coef_of_finite | (intros; apply GlobalTheory.CoefJoin.coef_of_finite <;> assumption)
