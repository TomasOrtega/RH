import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPointHeightDualAndLinearComb.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.point_height_dual_and_linear_comb : GlobalTheory.Published.ArExists → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ x : X, IsAlgPt x → (∀ (L : HermLB p) (a : ℝ), IsPtHt L x a → IsPtHt L.dual x (-a)) ∧ ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (a : ι → ℝ), (∀ i, IsPtHt (L i) x (a i)) → ∀ n : ι → ℤ, IsPtHt (ArInt.comb L n) x (∑ i, (n i : ℝ) * a i) := by
  first | exact @GlobalTheory.PtHtComb.isPtHt_dual_comb | exact GlobalTheory.PtHtComb.isPtHt_dual_comb | (intros; apply GlobalTheory.PtHtComb.isPtHt_dual_comb <;> assumption)
