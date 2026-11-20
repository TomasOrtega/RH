import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFromLocalizationsAway
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVanishingFromLocalizationsAway.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_local_covering : ∀ (B : Type) [CommRing B] (s : Set B), (∀ P : PrimeSpectrum B, ∃ f ∈ s, f ∉ P.asIdeal) → ∀ b : B, (∀ f ∈ s, algebraMap B (Localization.Away f) b = 0) → b = 0 := by
  first | exact @GlobalTheory.PDiv.eq_zero_of_away_eq_zero_of_forall_prime | exact GlobalTheory.PDiv.eq_zero_of_away_eq_zero_of_forall_prime | (intros; apply GlobalTheory.PDiv.eq_zero_of_away_eq_zero_of_forall_prime <;> assumption)
