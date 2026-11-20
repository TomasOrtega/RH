import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHtDiag.exists_isArithHeight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsArithHeightEqMixedHeightDiagonal.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal : ArchInteg → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ T, IsMix p (D + 1) T → ∀ N : HermLB p, ∃ h : X → ℝ, N.IsArithHeight h ∧ ∀ (x : X) (d : ℕ), HasDim x d → h x = T d (fun _ => N) x := by
  first | exact @GlobalTheory.MixHtDiag.exists_isArithHeight | exact GlobalTheory.MixHtDiag.exists_isArithHeight | (intros; apply GlobalTheory.MixHtDiag.exists_isArithHeight <;> assumption)
