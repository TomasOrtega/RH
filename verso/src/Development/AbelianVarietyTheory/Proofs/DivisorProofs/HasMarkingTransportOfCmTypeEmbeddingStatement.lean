import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasMarkingTransportOfCmTypeEmbedding.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.hasMarkingTransport_of_cmType_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  first | exact @GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | exact GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | (intros; apply GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb <;> assumption)
