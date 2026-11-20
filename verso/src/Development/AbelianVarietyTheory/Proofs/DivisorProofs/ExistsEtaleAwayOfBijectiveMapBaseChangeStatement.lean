import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfBijectiveMapBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEtaleAwayOfBijectiveMapBaseChange.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_etale_away_of_bijective_kaehler_mapBaseChange : ∀ (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C] [Algebra.Smooth A B] (Q : Ideal B) [Q.IsPrime], Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) → ∃ f : B, f ∉ Q ∧ Algebra.Etale C (Localization.Away f) := by
  first | exact @GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange | exact GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange | (intros; apply GlobalTheory.Mum.exists_etale_away_of_bijective_mapBaseChange <;> assumption)
