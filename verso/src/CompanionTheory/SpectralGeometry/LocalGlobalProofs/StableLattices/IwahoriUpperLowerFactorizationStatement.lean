import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization
import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FIwahoriUpperLowerFactorization.lean&line=224#L224)
-/
theorem _root_.GlobalTheory.T.iwahori_upper_lower_factorization : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt → ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J → ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧ GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | exact GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss <;> assumption)
