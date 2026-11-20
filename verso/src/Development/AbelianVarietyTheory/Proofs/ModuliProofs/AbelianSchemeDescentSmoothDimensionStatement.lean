import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | exact GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | (intros; apply GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.abelian_scheme_descent_smooth_dimension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | exact GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend | (intros; apply GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend <;> assumption)
