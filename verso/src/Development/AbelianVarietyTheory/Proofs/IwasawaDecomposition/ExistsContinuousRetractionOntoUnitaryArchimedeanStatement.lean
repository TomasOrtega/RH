import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefU.exists_embRet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsContinuousRetractionOntoUnitaryArchimedean.lean&line=182#L182)
-/
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧ ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.exists_embRet | exact GlobalTheory.DefU.exists_embRet | (intros; apply GlobalTheory.DefU.exists_embRet <;> assumption)
