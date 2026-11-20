import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneLeFinrankSecM
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolSection.one_le_finrank_secM` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FOneLeFinrankSecM.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.one_le_finrank_secM_one_of_isAlgClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), 1 ≤ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) := by
  first | exact @GlobalTheory.PolSection.one_le_finrank_secM | exact GlobalTheory.PolSection.one_le_finrank_secM | (intros; apply GlobalTheory.PolSection.one_le_finrank_secM <;> assumption)
