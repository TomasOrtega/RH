import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ V hV`. Set `π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)` to `MvPolynomial.map (IsLocalRing.residue O)`. Establish `hπ : Function.Surjective π` using `MvPolynomial.map_surjective _ (IsLocalRing.residue_surjective)`. Use `⟨V.comap π, Ideal.comap_isPrime π V, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : IsLocalRing.residue O ϖ = 0` using `(IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)`.

Rewrite using `[Ideal.mem_comap]`. Establish `: π (C ϖ) = 0`. Simplify using `only [π, MvPolynomial.map_C, h0, map_zero]`. Rewrite using `[this]`. Conclude with `V.zero_mem`.

Conclude with `Ideal.map_comap_of_surjective π hπ V`.
-/
theorem SpecialIdealSurj.proof : SpecialIdealSurj.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ V hV
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hπ : Function.Surjective π :=
    MvPolynomial.map_surjective _ (IsLocalRing.residue_surjective)
  refine ⟨V.comap π, Ideal.comap_isPrime π V, ?_, ?_⟩
  · have h0 : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).2
        ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
    rw [Ideal.mem_comap]
    have : π (C ϖ) = 0 := by
      simp only [π, MvPolynomial.map_C, h0, map_zero]
    rw [this]
    exact V.zero_mem
  · exact Ideal.map_comap_of_surjective π hπ V

end GroundTheory.Heights₂.Heights.NumbersDVR
