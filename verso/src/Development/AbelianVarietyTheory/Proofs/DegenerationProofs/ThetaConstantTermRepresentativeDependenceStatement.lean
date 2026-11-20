import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ex.txT_shift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FThetaConstantTermRepresentativeDependence.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.thetaConstantTerm_representative_dependence : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  first | exact @GlobalTheory.Ex.txT_shift | exact GlobalTheory.Ex.txT_shift | (intros; apply GlobalTheory.Ex.txT_shift <;> assumption)
