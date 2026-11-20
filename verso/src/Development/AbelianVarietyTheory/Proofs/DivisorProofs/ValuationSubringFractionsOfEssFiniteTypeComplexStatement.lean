import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringFractionsOfEssFiniteTypeComplex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.valuationSubring_fractions_of_essFiniteType` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationSubringFractionsOfEssFiniteTypeComplex.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.valuationSubring_fractions_of_essFiniteType_complex : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (hψ : ∀ a, ψ a ∈ V), (ψ.codRestrict V hψ).EssFiniteType → ∃ s₀ : Finset L, (∀ x ∈ s₀, x ∈ V) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.valuationSubring_fractions_of_essFiniteType | exact GlobalTheory.valuationSubring_fractions_of_essFiniteType | (intros; apply GlobalTheory.valuationSubring_fractions_of_essFiniteType <;> assumption)
