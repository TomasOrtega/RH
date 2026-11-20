import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists
import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCongruenceEndomorphismInverseExists.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.congruence_endomorphism_inverse_exists : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 → ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | exact GlobalTheory.CompanionTheory.Iwahori.CongUnit.main | (intros; apply GlobalTheory.CompanionTheory.Iwahori.CongUnit.main <;> assumption)
