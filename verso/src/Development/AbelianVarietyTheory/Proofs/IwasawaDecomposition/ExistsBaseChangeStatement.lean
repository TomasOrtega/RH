import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.EigFrame.exists_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsBaseChange.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_eigFrame_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  first | exact @GlobalTheory.ShFam.EigFrame.exists_baseChange | exact GlobalTheory.ShFam.EigFrame.exists_baseChange | (intros; apply GlobalTheory.ShFam.EigFrame.exists_baseChange <;> assumption)
