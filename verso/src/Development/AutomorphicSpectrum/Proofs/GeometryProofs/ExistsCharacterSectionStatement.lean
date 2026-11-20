import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCharacterSection
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.exists_character_section` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsCharacterSection.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_character_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_character_section | exact GlobalTheory.CompanionTheory.Relay.exists_character_section | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_character_section <;> assumption)
