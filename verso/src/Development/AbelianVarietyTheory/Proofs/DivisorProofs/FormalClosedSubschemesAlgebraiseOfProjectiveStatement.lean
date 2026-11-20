import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalClosedSubschemesAlgebraiseOfProjective.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isProjBy | exact GlobalTheory.FormalAlg.alg_of_isProjBy | (intros; apply GlobalTheory.FormalAlg.alg_of_isProjBy <;> assumption)
