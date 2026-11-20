import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.GradedDiv.exists_gr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsGradedLineDivisorsFullFlag.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.exists_graded_line_divisors_full_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  first | exact @GlobalTheory.ShFam.GradedDiv.exists_gr | exact GlobalTheory.ShFam.GradedDiv.exists_gr | (intros; apply GlobalTheory.ShFam.GradedDiv.exists_gr <;> assumption)
