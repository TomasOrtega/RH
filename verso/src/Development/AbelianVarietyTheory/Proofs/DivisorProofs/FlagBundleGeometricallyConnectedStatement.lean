import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGeometricallyConnected
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagBundleGeometricallyConnected.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.flag_bundle_geometrically_connected : ∀ (F : Type) [Field F] (G : Scheme.{0}) (s : G ⟶ Sp F) (ι : Type) [Fintype ι] (E : ι → (Sp F).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → IsFlagBundle s E r fl → GeometricallyConnected s := by
  first | exact @GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle | exact GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle | (intros; apply GlobalTheory.FlagOverField.geometricallyConnected_of_isFlagBundle <;> assumption)
