import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
Introduce `hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y y' f hf`. Use `hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_` and prove the remaining obligations. Establish `hf'` using `hL.1 y' f hf`. Rewrite using `[← hL.2 (y * y') Ψ hΨ f hf, ← hL.2 y Ψ hΨ _ hf', map_mul, map_mul, Module.End.mul_apply]`. Use `congr 2`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hL.2 y' Ψ hΨ f hf`.
-/
theorem locMul_of : TensInj → LocMul := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y y' f hf
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx _ _ fun Ψ hΨ => ?_
  have hf' := hL.1 y' f hf
  rw [← hL.2 (y * y') Ψ hΨ f hf, ← hL.2 y Ψ hΨ _ hf', map_mul, map_mul, Module.End.mul_apply]
  congr 2
  apply Subtype.ext
  exact hL.2 y' Ψ hΨ f hf

end PositivityTheory.Rg.Sw.Glob
