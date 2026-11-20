import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Introduce `K _ _ e n v`. Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Set `R` to `ParDVR e n v`. Set `E` to `(IsLocalRing.maximalIdeal R).ResidueField`. Set `k` to `v.asIdeal.ResidueField`.

Set `_ : Algebra k E` to `(resToKappa e n v).toAlgebra`. Rewrite using `[algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]`. Introduce `p hp`. Take `⟨q, rfl⟩` from `MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal) p`. Establish `hext : (eval₂Hom ((algebraMap k E).comp (algebraMap (𝓞 K) k)) (parYκ e n v)) = (algebraMap R E).comp (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R)`.

Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) R]`. Conclude with `Ideal.ResidueField.map_algebraMap _ _ _ _ a`. Simplify using `[parYκ, parY, R, E]`.

Establish `key : aeval (parYκ e n v) (MvPolynomial.map (algebraMap (𝓞 K) k) q) = algebraMap R E (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R q)`. Rewrite using `[aeval_def, eval₂_map]`. Conclude with `congrArg (fun φ => φ q) hext`. Rewrite `hp` using `[key, Ideal.algebraMap_residueField_eq_zero]`. Establish `hq : q ∈ parPrime e n v`.

Establish `h2 : (IsLocalRing.maximalIdeal R).comap (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) = parPrime e n v` using `Localization.AtPrime.under_maximalIdeal`. Rewrite using `[← h2]`. Conclude with `hp`. Rewrite `hq` using `[parPrime, MvPolynomial.mem_map_C_iff]`. Use extensionality with `m`.

Rewrite using `[coeff_map, coeff_zero]`. Conclude with `Ideal.algebraMap_residueField_eq_zero.mpr (hq m)`.
-/
theorem ResidueAlgIndep.proof : ResidueAlgIndep.Statement := by
  intro K _ _ e n v
  have : v.asIdeal.IsMaximal := v.isMaximal
  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let _ : Algebra k E := (resToKappa e n v).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal) p

  have hext : (eval₂Hom ((algebraMap k E).comp (algebraMap (𝓞 K) k)) (parYκ e n v)) =
      (algebraMap R E).comp (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) R]
      exact Ideal.ResidueField.map_algebraMap _ _ _ _ a
    · simp [parYκ, parY, R, E]
  have key : aeval (parYκ e n v) (MvPolynomial.map (algebraMap (𝓞 K) k) q) =
      algebraMap R E (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R q) := by
    rw [aeval_def, eval₂_map]
    exact congrArg (fun φ => φ q) hext
  rw [key, Ideal.algebraMap_residueField_eq_zero] at hp
  have hq : q ∈ parPrime e n v := by
    have h2 : (IsLocalRing.maximalIdeal R).comap (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R) =
        parPrime e n v :=
      Localization.AtPrime.under_maximalIdeal
    rw [← h2]
    exact hp
  rw [parPrime, MvPolynomial.mem_map_C_iff] at hq
  ext m
  rw [coeff_map, coeff_zero]
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hq m)

end

end GroundTheory.Heights₂.Heights.Vertical
