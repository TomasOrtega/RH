import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutation
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPowOnePowTwoCommutation.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.pow_one_pow_two_commutation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange <;> assumption)
