import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X`. Take `⟨c, hc, hAc⟩` from `hA II Ψ K ι Ω E D O Lt X`. Use `⟨c, hc, fun B p q t δ hs hl hqp => ⟨hS II Ψ K ι Ω E D O Lt X B p q t hs, fun z hz w hw => ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `X.S.R.cover (X.M.proj z)`. Establish `hk' : X.M.proj z ∈ X.S.R.mid k` using `X.S.R.inner_subset_mid k hk`.

Take `⟨v, hv, heq⟩` from `hL II Ψ K ι Ω E D O Lt X B p q t hs z hz w hw k hk'`. Establish `h1` using `hl k _ hk' v`. Establish `h2` using `hAc z hz w k hk' v hv`. Use `show 0 ≤ levi _ z w`. Rewrite using `[heq]`.

Establish `hq : (0 : ℝ) ≤ q` using `Nat.cast_nonneg q`. Establish `hp : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`. Establish `hv2 : 0 ≤ ‖v‖ ^ 2` using `sq_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hp, mul_le_mul_of_nonneg_right hqp hv2]`.
-/
theorem NbarChartSemipos.proof (hS : NbarSmooth.Statement) (hL : NbarLeviChart.Statement)
    (hA : APrimeChartMargin.Statement) : NbarChartSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨c, hc, hAc⟩ := hA II Ψ K ι Ω E D O Lt X
  refine ⟨c, hc, fun B p q t δ hs hl hqp => ⟨hS II Ψ K ι Ω E D O Lt X B p q t hs, fun z hz w hw => ?_⟩⟩
  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hk' : X.M.proj z ∈ X.S.R.mid k := X.S.R.inner_subset_mid k hk
  obtain ⟨v, hv, heq⟩ := hL II Ψ K ι Ω E D O Lt X B p q t hs z hz w hw k hk'
  have h1 := hl k _ hk' v
  have h2 := hAc z hz w k hk' v hv
  show 0 ≤ levi _ z w
  rw [heq]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hp,
    mul_le_mul_of_nonneg_right hqp hv2]

end GroundTheory.Heights₂.Heights.LowerBoundFree
