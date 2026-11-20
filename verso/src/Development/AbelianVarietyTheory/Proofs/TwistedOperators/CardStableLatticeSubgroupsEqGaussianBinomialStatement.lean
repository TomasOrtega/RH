import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCardStableLatticeSubgroupsEqGaussianBinomial.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  first | exact @GlobalTheory.LatCountGauss.card_latCount | exact GlobalTheory.LatCountGauss.card_latCount | (intros; apply GlobalTheory.LatCountGauss.card_latCount <;> assumption)
