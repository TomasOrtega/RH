import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaEquivariantFrobenius
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FAlphaEquivariantFrobenius.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.alpha_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | exact GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act <;> assumption)
