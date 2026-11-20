import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeIsIsoOfMonoSameDimension.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.abelianScheme_isIso_of_mono_same_dimension : ∀ (S : Scheme.{0}) (B B' : Over S) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension g B'.hom → ∀ x : B ⟶ B', IsMonHom x → Mono x → IsIso x := by
  first | exact @GlobalTheory.AbMonoIsoAny.isIso_of_mono | exact GlobalTheory.AbMonoIsoAny.isIso_of_mono | (intros; apply GlobalTheory.AbMonoIsoAny.isIso_of_mono <;> assumption)
