import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndicatorTsumOne
import Mathlib
open MeasureTheory
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fundamentalDomain_count_ae_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFundamentalDomainIndicatorTsumOne.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.fundamental_domain_indicator_tsum_one : ∀ {G : Type} [Group G] [MeasurableSpace G] (μG : Measure G) (Q : Subgroup G) (𝓓 𝓓₀ : Set G),
    Countable Q → (∀ g : G, Measurable (g * ·)) → μG.IsMulLeftInvariant →
    IsFundamentalDomain Q 𝓓 μG → MeasurableSet 𝓓₀ → 𝓓₀ ⊆ 𝓓 → μG (𝓓 \ 𝓓₀) = 0 →
    ∀ᵐ y ∂μG, ∑' q : Q, 𝓓₀.indicator (1 : G → ENNReal) ((q : G) * y) = 1 := by
  first | exact @GlobalTheory.fundamentalDomain_count_ae_eq_one | exact GlobalTheory.fundamentalDomain_count_ae_eq_one | (intros; apply GlobalTheory.fundamentalDomain_count_ae_eq_one <;> assumption)
