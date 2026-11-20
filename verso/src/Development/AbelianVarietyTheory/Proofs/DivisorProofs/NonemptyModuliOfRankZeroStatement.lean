import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UCanon.RankZero.nonempty_moduli` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyModuliOfRankZero.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.nonempty_moduli_of_rank_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H), D.p + D.q = 0 → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.UCanon.RankZero.nonempty_moduli | exact GlobalTheory.UCanon.RankZero.nonempty_moduli | (intros; apply GlobalTheory.UCanon.RankZero.nonempty_moduli <;> assumption)
