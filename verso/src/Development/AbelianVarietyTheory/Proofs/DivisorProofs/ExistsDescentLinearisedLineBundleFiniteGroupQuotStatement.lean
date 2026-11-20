import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
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
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDescentLinearisedLineBundleFiniteGroupQuot.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  first | exact @GlobalTheory.QuotDescent.descent | exact GlobalTheory.QuotDescent.descent | (intros; apply GlobalTheory.QuotDescent.descent <;> assumption)
