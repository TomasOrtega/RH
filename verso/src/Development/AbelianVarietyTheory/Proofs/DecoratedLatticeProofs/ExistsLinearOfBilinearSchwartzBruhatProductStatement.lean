import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsLinearOfBilinearSchwartzBruhatProduct.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  first | exact @GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | exact GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | (intros; apply GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB <;> assumption)
