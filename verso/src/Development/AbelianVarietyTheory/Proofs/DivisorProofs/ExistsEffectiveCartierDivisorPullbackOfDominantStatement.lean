import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cartier.exists_pull_dominant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEffectiveCartierDivisorPullbackOfDominant.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.exists_effective_cartierDivisorPullback_of_dominant : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  first | exact @GlobalTheory.Cartier.exists_pull_dominant | exact GlobalTheory.Cartier.exists_pull_dominant | (intros; apply GlobalTheory.Cartier.exists_pull_dominant <;> assumption)
