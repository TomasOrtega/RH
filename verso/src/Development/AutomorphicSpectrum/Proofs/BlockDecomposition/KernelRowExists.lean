import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n _ _ μ _ E _ Ω T F c hS h hh v`. Establish `hS'` using `hS`. Take `⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩` from `hS'`. Take `⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩` from `hFac h hh`. Take `⟨κ, hκ, hrow⟩` from `hEv n μ E Ω T F c hS h₁ r₁ v`.

Take `⟨C₁, hC₁⟩` from `hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s`. Take `⟨C₂, hC₂⟩` from `hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂`. Take `⟨f, hfS, hfE, hfc, -⟩` from `hC₁ κ hκ`. Use `⟨f, hfS, hfE, ?_⟩` and prove the remaining obligations. Introduce `φ f' hφS hφE hf'S hf'E hf'`.

Take `⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩` from `hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)`. Establish `hmul : cls μ f' = F.Φ h₁ (cls μ φ₂)`. Rewrite using `[hf', F.map_mul, hφ₂c]`. Both sides reduce to the same expression. Rewrite using `[hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]`.

Conclude with `hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul`.
-/
theorem rowExists_of_factor (hFac : FactorRapid) (hEv : EvAdj) : RowExists := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  have hS' := hS
  obtain ⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩ := hS'
  obtain ⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩ := hFac h hh
  obtain ⟨κ, hκ, hrow⟩ := hEv n μ E Ω T F c hS h₁ r₁ v
  obtain ⟨C₁, hC₁⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s
  obtain ⟨C₂, hC₂⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂
  obtain ⟨f, hfS, hfE, hfc, -⟩ := hC₁ κ hκ
  refine ⟨f, hfS, hfE, ?_⟩
  intro φ f' hφS hφE hf'S hf'E hf'
  obtain ⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩ := hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)
  have hmul : cls μ f' = F.Φ h₁ (cls μ φ₂) := by
    rw [hf', F.map_mul, hφ₂c]
    rfl
  rw [hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]
  exact hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul

end GlobalTheory.CompanionTheory.KerFc
