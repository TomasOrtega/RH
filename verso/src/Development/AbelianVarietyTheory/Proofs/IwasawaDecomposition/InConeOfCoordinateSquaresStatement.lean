import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfCoordinateSquares
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FInConeOfCoordinateSquares.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.inCone_of_coordinate_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Dg : DegPre R) (m : ℕ) (t : Fin m → R) (k : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ Dg.X), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) →
    (∀ y, ∃ (r : R) (u : Rˣ), PsiCoord Dg y r ∧ r ^ 2 = u * ∏ i, t i ^ (k * (γ i y y).toNat)) → InCone Dg γ := by
  first | exact @GlobalTheory.SiegLoc.inCone_of_sq_monomial | exact GlobalTheory.SiegLoc.inCone_of_sq_monomial | (intros; apply GlobalTheory.SiegLoc.inCone_of_sq_monomial <;> assumption)
