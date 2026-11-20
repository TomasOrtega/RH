import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper
import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FUpperTriangularInverseIsUpper.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.upper_triangular_inverse_is_upper : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | exact GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv | (intros; apply GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv <;> assumption)
