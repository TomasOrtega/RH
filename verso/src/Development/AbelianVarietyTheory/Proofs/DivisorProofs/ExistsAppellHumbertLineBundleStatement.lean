import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAppellHumbertLineBundle.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_appell_humbert_line_bundle : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L₀ : LB A.left) (g : ℕ) (u₀ : HolUnif A L₀ g)
    (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.ex = u₀.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.exists_isFactorAH_frame_of_unif | exact GlobalTheory.exists_isFactorAH_frame_of_unif | (intros; apply GlobalTheory.exists_isFactorAH_frame_of_unif <;> assumption)
