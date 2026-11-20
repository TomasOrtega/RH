import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StatementPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarizedAbelianShortExactStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeConjCh2

/- English proof (translation)
Introduce `h₀ h₁ h₂ p _ T _ hT A _ g hA hg hc`. Take `⟨S₁, S₂, e₁, e₂, hV, ⟨i₂⟩, ⟨i₁⟩, ⟨i₃⟩, ⟨j₁⟩, ⟨j₃⟩⟩` from `GlobalTheory.T.principally_polarized_abelian_short_exact h₀ h₁ h₂ p T hT A g hA hg hc`. Use `haveI : IsIntegral T := hT.1`. Establish `hT' : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.IsProjSurface (ZMod p) T` using `⟨hT.1, hT.2.1, hT.2.2⟩`. Take `⟨hAdd, hDual, hFrob⟩` from `GlobalTheory.T.statement_prime_field p T hT'`.

Establish `hω : GlobalTheory.VB.IsVB (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) g` using `GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g`. Establish `hω'` using `hω.dual`. Establish `hF` using `GlobalTheory.VB.IsVB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) hω`. Establish `hF'` using `GlobalTheory.VB.IsVB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) hω'`. Establish `a₁` using `hAdd S₁ e₁ g (2 * g) g (hω.of_iso i₁.symm) hV (hω'.of_iso i₃.symm)`.

Establish `a₂` using `hAdd S₂ e₂ g (2 * g) g (hF'.of_iso j₁.symm) (hV.of_iso i₂) (hF.of_iso j₃.symm)`. Rewrite `a₁` using `[GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₁, GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₃, hDual _ g hω]`. Rewrite `a₂` using `[GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr j₁, GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr j₃, hFrob _ g hω', hFrob _ g hω, hDual _ g hω, ← GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₂, a₁]`. Establish `hp : (1 : ℚ) < (p : ℚ) ^ 2`. Establish `: (2 : ℚ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).two_le`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hd : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 (ZMod p) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) = 0`. Establish `: ((p : ℚ) ^ 2 - 1) * GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 (ZMod p) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) = 0`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. Rewrite `hd` using `[GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_eq hω]`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.degCh2]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality →
    GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes := by
  intro h₀ h₁ h₂ p _ T _ hT A _ g hA hg hc
  obtain ⟨S₁, S₂, e₁, e₂, hV, ⟨i₂⟩, ⟨i₁⟩, ⟨i₃⟩, ⟨j₁⟩, ⟨j₃⟩⟩ :=
    GlobalTheory.T.principally_polarized_abelian_short_exact h₀ h₁ h₂ p T hT A g hA hg hc
  haveI : IsIntegral T := hT.1
  have hT' : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.IsProjSurface (ZMod p) T := ⟨hT.1, hT.2.1, hT.2.2⟩
  obtain ⟨hAdd, hDual, hFrob⟩ := GlobalTheory.T.statement_prime_field p T hT'
  have hω : GlobalTheory.VB.IsVB (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) g := GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g
  have hω' := hω.dual
  have hF := GlobalTheory.VB.IsVB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) hω
  have hF' := GlobalTheory.VB.IsVB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) hω'
  have a₁ := hAdd S₁ e₁ g (2 * g) g (hω.of_iso i₁.symm) hV (hω'.of_iso i₃.symm)
  have a₂ := hAdd S₂ e₂ g (2 * g) g (hF'.of_iso j₁.symm) (hV.of_iso i₂) (hF.of_iso j₃.symm)
  rw [GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₁, GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₃, hDual _ g hω] at a₁
  rw [GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr j₁, GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr j₃, hFrob _ g hω',
    hFrob _ g hω, hDual _ g hω, ← GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_congr i₂, a₁] at a₂
  have hp : (1 : ℚ) < (p : ℚ) ^ 2 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    nlinarith
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 (ZMod p) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) = 0 := by
    have : ((p : ℚ) ^ 2 - 1) * GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2 (ZMod p) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.degCh2_eq hω] at hd
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.degCh2]
  push_cast
  linarith

end GlobalTheory.HodgeConjCh2
