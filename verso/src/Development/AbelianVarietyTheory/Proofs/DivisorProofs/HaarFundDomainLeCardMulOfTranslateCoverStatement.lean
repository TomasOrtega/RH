import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundDomainLeCardMulOfTranslateCover
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHaarFundDomainLeCardMulOfTranslateCover.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  first | exact @GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | exact GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | (intros; apply GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover <;> assumption)
