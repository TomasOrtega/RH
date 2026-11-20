import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLieModelActionBaseChange.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.lie_model_action_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ S), ∃ (n : ℕ) (M : LieModel t.G x (Fin n → R)) (ρ : 𝓞 E →+* Module.End R (Fin n → R)), M.IsActOf t.act.act ρ ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : Sp R' ⟶ S), x' = spMap f ≫ x → ∃ (M' : LieModel t.G x' (Fin n → R')) (ρ' : 𝓞 E →+* Module.End R' (Fin n → R')), M'.IsActOf t.act.act ρ' ∧ (∀ u, (M'.pt (f ∘ u)).left = spMap (dualMap f) ≫ (M.pt u).left) ∧ ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange | exact GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange <;> assumption)
