import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r E _ _ _ Dm J h g₀ hg₀`. Set `b` to `Module.finBasis ℂ E`. Set `ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ` to `fun i => LinearMap.toContinuousLinearMap (b.coord i)`. Use `choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀`. Use `⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩` and prove the remaining obligations.

Use `ContDiffOn.sum fun i _ => ?_` and prove the remaining obligations. Conclude with `((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const`. Introduce `g hg hgG`. Establish `hg'` using `Set.mem_iInter.1 hg`. Use `conv_lhs => rw [← b.sum_repr (J g)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hJF i g (hg' i) hgG]`. Both sides reduce to the same expression.
-/
theorem smooth_of_coefficients_holds : SmoothOfCoeffs := by
  intro k r E _ _ _ Dm J h g₀ hg₀
  let b := Module.finBasis ℂ E
  let ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    exact ((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const
  · intro g hg hgG
    have hg' := Set.mem_iInter.1 hg
    conv_lhs => rw [← b.sum_repr (J g)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hJF i g (hg' i) hgG]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
