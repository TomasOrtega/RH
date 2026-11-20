import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAlgebraicWeightOfAutomorphicDefiniteUnitar.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam := by
  first | exact @GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | exact GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU | (intros; apply GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU <;> assumption)
