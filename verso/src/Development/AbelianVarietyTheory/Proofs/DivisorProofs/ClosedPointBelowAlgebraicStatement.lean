import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointBelowAlgebraic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FClosedPointBelowAlgebraic.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.closed_point_below_algebraic : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (p : Sp Qb ⟶ Y.X), IsClosed ({below p} : Set Y.X) := by
  first | exact @GlobalTheory.Mean4O.isClosed_below_algebraic | exact GlobalTheory.Mean4O.isClosed_below_algebraic | (intros; apply GlobalTheory.Mean4O.isClosed_below_algebraic <;> assumption)
