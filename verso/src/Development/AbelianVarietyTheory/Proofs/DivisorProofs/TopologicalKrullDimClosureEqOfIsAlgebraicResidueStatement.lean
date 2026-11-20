import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTopologicalKrullDimClosureEqOfIsAlgebraicResidue.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  first | exact @GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | exact GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | (intros; apply GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic <;> assumption)
