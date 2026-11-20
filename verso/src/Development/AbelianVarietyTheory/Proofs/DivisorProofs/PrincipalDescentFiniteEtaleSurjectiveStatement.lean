import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDescentFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalDescentFiniteEtaleSurjective.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.principal_descent_finite_etale_surjective : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  first | exact @GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | exact GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | (intros; apply GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale <;> assumption)
