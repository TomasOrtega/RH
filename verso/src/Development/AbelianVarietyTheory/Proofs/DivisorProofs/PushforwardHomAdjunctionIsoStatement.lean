import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardHomAdjunctionIso
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPushforwardHomAdjunctionIso.lean&line=214#L214)
-/
theorem _root_.GlobalTheory.T.pushforward_hom_adjunction_iso : ∀ (X Y : Scheme.{0}) (ρ : Y ⟶ X) (W : X.Modules) (N : Y.Modules), Nonempty ((Scheme.Modules.pushforward ρ).obj (homMod ((Scheme.Modules.pullback ρ).obj W) N) ≅ homMod W ((Scheme.Modules.pushforward ρ).obj N)) := by
  first | exact @GlobalTheory.HomPull.nonempty_pushforward_homMod_iso | exact GlobalTheory.HomPull.nonempty_pushforward_homMod_iso | (intros; apply GlobalTheory.HomPull.nonempty_pushforward_homMod_iso <;> assumption)
