import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsIsoMorphismRestrictOfIsProjOver.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver <;> assumption)
