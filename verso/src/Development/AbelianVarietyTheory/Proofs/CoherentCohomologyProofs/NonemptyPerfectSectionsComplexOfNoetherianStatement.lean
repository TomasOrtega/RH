import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AbLaw.nonempty_perf_of_noetherian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FNonemptyPerfectSectionsComplexOfNoetherian.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R], Flat f → IsProjBy f → ∀ M : LB Y, M.IsLB → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.AbLaw.nonempty_perf_of_noetherian | exact GlobalTheory.AbLaw.nonempty_perf_of_noetherian | (intros; apply GlobalTheory.AbLaw.nonempty_perf_of_noetherian <;> assumption)
