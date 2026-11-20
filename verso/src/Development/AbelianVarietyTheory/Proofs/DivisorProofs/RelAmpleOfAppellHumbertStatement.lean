import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LefschetzAmple.relAmple_of_isAH` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelAmpleOfAppellHumbert.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.rel_ample_of_appell_humbert : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → Out.RelAmple A M := by
  first | exact @GlobalTheory.LefschetzAmple.relAmple_of_isAH | exact GlobalTheory.LefschetzAmple.relAmple_of_isAH | (intros; apply GlobalTheory.LefschetzAmple.relAmple_of_isAH <;> assumption)
