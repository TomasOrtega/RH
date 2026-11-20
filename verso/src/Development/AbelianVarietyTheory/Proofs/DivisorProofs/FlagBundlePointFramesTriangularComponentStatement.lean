import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VarFlag.carriesTri` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagBundlePointFramesTriangularComponent.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.flagBundlePointFramesTriangular_component : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C := by
  first | exact @GlobalTheory.VarFlag.carriesTri | exact GlobalTheory.VarFlag.carriesTri | (intros; apply GlobalTheory.VarFlag.carriesTri <;> assumption)
