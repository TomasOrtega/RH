import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
/- English proof (citation)
Apply `GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCoherentCohomologyProofs%2FCechLBHomologyEquivOfAffineCovers.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ' : Type) [LinearOrder κ'] [Fintype κ'] (D' : κ' → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, IsAffineOpen (D' i)) → ⨆ i, D' i = ⊤ → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cechLB f M D').homology n) := by
  first | exact @GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers | exact GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers | (intros; apply GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers <;> assumption)
