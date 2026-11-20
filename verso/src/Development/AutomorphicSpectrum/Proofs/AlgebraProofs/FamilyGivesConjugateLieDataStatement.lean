import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieData
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFamilyGivesConjugateLieData.lean&line=462#L462)
-/
theorem _root_.GlobalTheory.T.family_gives_conjugate_lie_data : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I → ∃ D : ConjData C p O d, (∀ a, D.ρ a = rho F.B a) ∧ ∀ i u, u ∈ D.lie i ↔ ∀ j, C.v i ((lin (F.ψ i) 1).mulVec u j) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj | exact GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Fam.family_conj <;> assumption)
