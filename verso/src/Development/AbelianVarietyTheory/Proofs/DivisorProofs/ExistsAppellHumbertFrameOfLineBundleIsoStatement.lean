import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAppellHumbertFrameOfLineBundleIso.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left) (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso | exact GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso | (intros; apply GlobalTheory.TransportFrame.exists_holUnif_isFactorAH_of_lbIso; all_goals assumption)
