import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.TieBase.exists_tied` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLieEigenpartsFrameFamilyOverVariety.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  first | exact @GlobalTheory.ShFam.TieBase.exists_tied | exact GlobalTheory.ShFam.TieBase.exists_tied | (intros; apply GlobalTheory.ShFam.TieBase.exists_tied <;> assumption)
