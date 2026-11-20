import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Introduce `z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone`. Use `hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone` and prove the remaining obligations. Introduce `f w σ hf hw hσ hadj hone hcf hcw hcσ`. Take `⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩` from `hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone`. Use `hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_` and prove the remaining obligations.

Conclude with `hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar (hcG hcf) (hcD hcw) (hcS hcf hcσ)`.
-/
theorem dens (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCut : CutoffStatement n M) (hUR : UnweightRelStatement n M)
    (hUB : UnweightBackStatement n M) (hLoc : LocalizeStatement n M)
    (hCh : ChartFlatStatement n M) : DensStatement n M := by
  intro z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone
  refine hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone
  intro f w σ hf hw hσ hadj hone hcf hcw hcσ
  obtain ⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩ :=
    hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone
  refine hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_
  exact hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar
    (hcG hcf) (hcD hcw) (hcS hcf hcσ)

end

end ReciprocityTheory.L2DbarEstimates.F
