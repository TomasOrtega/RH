import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimT
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLinearClosedImmersionProjectiveSpaceCodimT.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo : ∀ (F : Type) [Field F] (N : ℕ), ∃ ℓ : PSpace F N ⟶ PSpace F (N + 2), IsClosedImmersion ℓ ∧ ℓ ≫ PSpace.str F (N + 2) = PSpace.str F N ∧ ∀ y, 2 ≤ ringKrullDim ((PSpace F (N + 2)).presheaf.stalk (ℓ y)) := by
  first | exact @GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | exact GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk | (intros; apply GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk <;> assumption)
