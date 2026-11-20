import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegOfPeriodicOfIsRegSub
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRegOfPeriodicOfIsRegSub.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.isReg_of_periodic_of_isReg_sub' : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → ∀ i, IsReg u.ex (W i) (h i) := by
  first | exact @GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub | exact GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub | (intros; apply GlobalTheory.CechPer.isReg_of_periodic_of_isReg_sub <;> assumption)
