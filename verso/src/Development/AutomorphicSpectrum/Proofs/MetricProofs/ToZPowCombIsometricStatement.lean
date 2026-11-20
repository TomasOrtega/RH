import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FToZPowCombIsometric.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.toZ_pow_comb_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (H : ∀ (L : HermLB p) (τ : ℤ →+* ℂ), (wZ L t τ).IsCInf), (∀ (L : HermLB p) (m : ℕ), (toZ (L.pow m) t (H _)).Isometric ((toZ L t (H _)).pow m)) ∧ ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ), (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (H _)) n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb | exact GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb <;> assumption)
