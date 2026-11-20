import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsEvalKerKrullDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'`. Use `⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hW.1.2.2 k.1`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite `h` using `[fibreIdeal, RingHom.mem_ker, aeval_X]`.

Establish `hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W'`. Rewrite using `[← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]`. Conclude with `h`. Simplify using `using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX`. Rewrite using `[fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']`.

Simplify using the standard rewrite rules.
-/
theorem FibreDimensionZero.proof (h₁ : ArithmeticIntersectionFibreMultiHomogeneous.Statement) (h₂ : EvalKerKrullDim.Statement)
    (h₃ : FibreTranscendenceDegreeAlt.Statement) : FibreDimensionZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  refine ⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hW.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at h
    have hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  · rw [fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']
    simp

end GroundTheory.Heights₂.Heights.Inter
