import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegEighth.exists_polAV_sharpOver` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPolarisedE8ThetaPowerOverModuli.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  first | exact @GlobalTheory.SiegEighth.exists_polAV_sharpOver | exact GlobalTheory.SiegEighth.exists_polAV_sharpOver | (intros; apply GlobalTheory.SiegEighth.exists_polAV_sharpOver <;> assumption)
