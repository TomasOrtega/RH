import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeGraphOfDenseFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.lbIso_cube_of_dense` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FLbIsoCubeGraphOfDenseFibres.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.lbIso_cube_graph_of_dense_fibres : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (u : A ⟶ A), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.Rigidified A L → IsMonHom u → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (_ : IsCommMonObj G) (φ : G.left ⟶ A.left) (L' : LB G.left) (u' : G ⟶ G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ L'.IsLB ∧ LBIso L' (L.pull φ) ∧ u'.left ≫ φ = φ ≫ u.left ∧ LBIso L' (cubeLB G ![𝟙 G, u'] L')} → LBIso L (cubeLB A ![𝟙 A, u] L) := by
  first | exact @GlobalTheory.lbIso_cube_of_dense | exact GlobalTheory.lbIso_cube_of_dense | (intros; apply GlobalTheory.lbIso_cube_of_dense <;> assumption)
