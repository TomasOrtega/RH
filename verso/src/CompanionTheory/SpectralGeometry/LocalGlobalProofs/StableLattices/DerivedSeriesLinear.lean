import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm

namespace GlobalTheory.CompanionTheory.BesselMapSm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n Hm H _ _ _ σ hσ u hu`. Establish `h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm` using `hσ.grp.2.1`. Take `⟨U, F, hUo, h1U, hF, hfF⟩` from `hu 1 h1`. Use `⟨fderiv ℝ F 1, fun X hX => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm` using `fun t => ex_mem_of_lie hX t`.

Establish `hd : HasDerivAt (fun t : ℝ => ex X t) X 0`. Simplify using `using hasDerivAt_mul_ex (1 : Mat n) X`. Establish `hl` using `hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF`. Conclude with `hl.deriv`.
-/
theorem dsLin : DsLin := by
  intro n Hm H _ _ _ σ hσ u hu
  have h1 : (1 : Mat n) ∈ Formalism.QuantumDeterminants.UH Hm := hσ.grp.2.1
  obtain ⟨U, F, hUo, h1U, hF, hfF⟩ := hu 1 h1
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have hmem : ∀ t : ℝ, ex X t ∈ Formalism.QuantumDeterminants.UH Hm := fun t => ex_mem_of_lie hX t
  have hd : HasDerivAt (fun t : ℝ => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex (1 : Mat n) X
  have hl := hasDerivAt_local (f := fun g => σ g u) hmem (ex_zero X) hd hUo h1U hF hfF
  exact hl.deriv

end GlobalTheory.CompanionTheory.BesselMapSm
