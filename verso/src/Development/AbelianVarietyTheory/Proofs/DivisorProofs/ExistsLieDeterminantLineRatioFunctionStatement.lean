import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.detLine_exists_ratio` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLieDeterminantLineRatioFunction.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.exists_lieDeterminantLine_ratio_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q), FrameCover t π s V (HermitianCompactForm.chi c τ) p q → IsSection t π s V (HermitianCompactForm.chi c τ) σ → NowhereZero t π s V (HermitianCompactForm.chi c τ) σ → IsSection t π s V (HermitianCompactForm.chi c τ) σ' → ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  first | exact @GlobalTheory.detLine_exists_ratio | exact GlobalTheory.detLine_exists_ratio | (intros; apply GlobalTheory.detLine_exists_ratio <;> assumption)
