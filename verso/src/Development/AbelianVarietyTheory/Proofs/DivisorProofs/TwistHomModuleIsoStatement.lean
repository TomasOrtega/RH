import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistHomModuleIso
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistHomModuleIso.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.twist_hom_module_iso : ∀ (Y : Scheme.{0}) (F G : Y.Modules) (M : LB Y), Nonempty (twist (homMod F G) M ≅ homMod F (twist G M)) := by
  first | exact @GlobalTheory.TwistHomMod.nonempty_iso | exact GlobalTheory.TwistHomMod.nonempty_iso | (intros; apply GlobalTheory.TwistHomMod.nonempty_iso <;> assumption)
