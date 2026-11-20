import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSurjectivePeriodMapAbelianVarietyLattice.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.surjective_periodMap_abelianVariety_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  first | exact @GlobalTheory.PerSurj.main | exact GlobalTheory.PerSurj.main | (intros; apply GlobalTheory.PerSurj.main <;> assumption)
