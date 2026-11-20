import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.EigStable.stable_of_isLocalRing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLieEigenspaceFrameStableOfIsLocalRing.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x), IsLocalRing R → f.Stable := by
  first | exact @GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | exact GlobalTheory.ShFam.EigStable.stable_of_isLocalRing | (intros; apply GlobalTheory.ShFam.EigStable.stable_of_isLocalRing <;> assumption)
