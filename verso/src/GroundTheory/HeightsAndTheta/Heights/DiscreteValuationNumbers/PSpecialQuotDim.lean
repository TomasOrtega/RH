import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ W hW`. Set `π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)` to `MvPolynomial.map (IsLocalRing.residue O)`. Establish `hsurj : Function.Surjective π` using `MvPolynomial.map_surjective _ IsLocalRing.residue_surjective`. Establish `hker : RingHom.ker π ≤ W`. Express the relevant statement in the definitionally equal form `RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W`.

Rewrite using `[MvPolynomial.ker_map, IsLocalRing.ker_residue, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hW`. Establish `hcomap : (specialIdeal W).comap π = W`. Express the relevant statement in the definitionally equal form `(W.map π).comap π = W`. Rewrite using `[Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]`.

Set `f` to `(Ideal.Quotient.mk (specialIdeal W)).comp π`. Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective.comp hsurj`. Establish `hkf : RingHom.ker f = W`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]`. Conclude with `(ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm`.
-/
theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
