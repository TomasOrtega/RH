import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefU.AU.existsUnique_hasWt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUniqueWeightDefiniteUnitaryAt.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.existsUnique_weight_definiteUnitary_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  first | exact @GlobalTheory.DefU.AU.existsUnique_hasWt | exact GlobalTheory.DefU.AU.existsUnique_hasWt | (intros; apply GlobalTheory.DefU.AU.existsUnique_hasWt <;> assumption)
