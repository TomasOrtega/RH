import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
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
Apply `GlobalTheory.WeakRes.weak_resolution` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeakResolutionOfPrincipalisation.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.weak_resolution_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W] (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n → ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧ IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  first | exact @GlobalTheory.WeakRes.weak_resolution | exact GlobalTheory.WeakRes.weak_resolution | (intros; apply GlobalTheory.WeakRes.weak_resolution <;> assumption)
