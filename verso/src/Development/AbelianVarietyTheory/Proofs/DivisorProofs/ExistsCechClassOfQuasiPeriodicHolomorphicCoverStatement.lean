import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechClassOfQuasiPeriodicHolomorphicCover
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCechClassOfQuasiPeriodicHolomorphicCover.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_cechClass_of_quasiPeriodic_holomorphic_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (K : Type) (W : K → A.left.Opens) (h : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), ⨆ i, W i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) (pre u.ex (W i))) → (∀ i j, IsReg u.ex (W i ⊓ W j) (h i - h j)) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i), h i (z + l) = h i z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.OfCover.exists_isPer | exact GlobalTheory.CechPer.OfCover.exists_isPer | (intros; apply GlobalTheory.CechPer.OfCover.exists_isPer <;> assumption)
