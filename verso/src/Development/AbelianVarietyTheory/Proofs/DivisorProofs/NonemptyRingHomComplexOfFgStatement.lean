import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyRingHomComplexOfFg.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.nonempty_ringHom_complex_of_fg' : ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  first | exact @GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | exact GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | (intros; apply GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg <;> assumption)
