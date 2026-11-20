import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultiplierIdealStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealLogResolutionStatement

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `hP k _ _ X _ _ _ p n hp hdim Δ η m G hL`. Establish `hne : (⊥ : Closeds X) ≠ ⊤`. Introduce `h`. Establish `hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X)` using `trivial`. Rewrite `hx` using `[← h]`.

Conclude with `hx`. Take `⟨Y, hYi, s, hsd, K, B, hR, -⟩` from `LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne`. Use `haveI := hYi`. Use `haveI := hsd`. Use `haveI := hR.smooth`.

Establish `hsm : Smooth (s ≫ p)` using `SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)`. Take `⟨-, -, hYn⟩` from `isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm`. Use `haveI := hYn`. Take `⟨J, hJ⟩` from `MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR`. Conclude with `⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩`.
-/
theorem exists_isMultIdeal_support_iff_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), IsLogMult p n Δ η m G → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J ∧ ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ η m G hL
  have hne : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    have hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, hYi, s, hsd, K, B, hR, -⟩ :=
    LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne
  haveI := hYi
  haveI := hsd
  haveI := hR.smooth
  have hsm : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)
  obtain ⟨-, -, hYn⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm
  haveI := hYn
  obtain ⟨J, hJ⟩ := MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR
  exact ⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩

end GlobalTheory.Discrepancy
