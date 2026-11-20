import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMumfordBundlePullbackTrivialOfImFormInt.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  first | exact @GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | exact GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | (intros; apply GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int <;> assumption)
