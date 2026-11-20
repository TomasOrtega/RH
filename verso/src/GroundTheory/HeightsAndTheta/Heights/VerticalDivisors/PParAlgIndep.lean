import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Use `MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C, eval₂Hom_C]`. Rewrite using `[kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]`. Simplify using `[parYF]`.
-/
theorem eval_parYF_comp (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    (eval₂Hom (kToFrac K e n) (parYF K e n)).comp
        (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (MvPolynomial (Par e n) K)) =
      algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) := by
  refine MvPolynomial.ringHom_ext (fun x => ?_) (fun p => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.algebraMap_def, map_C,
      eval₂Hom_C]
    rw [kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  · simp [parYF]

/- English proof (translation)
Introduce `K _ _ e n`. Set `_` to `(kToFrac K e n).toAlgebra`. Rewrite using `[algebraicIndependent_iff_injective_aeval]`. Express the relevant statement in the definitionally equal form `Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))`. Set `M : Submonoid (MvPolynomial (Par e n) (𝓞 K))` to `(nonZeroDivisors (𝓞 K)).map C`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective M z`. Establish `h` using `IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s`. Establish `hc` using `eval_parYF_comp K e n`.

Establish `ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0`. Rewrite using `[← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]`. Establish `ha0 : a = 0` using `IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)`. Substitute `ha0` using the available equality. Conclude with `IsLocalization.mk'_zero _`.
-/
theorem ParAlgIndep.proof : ParAlgIndep.Statement := by
  intro K _ _ e n
  let _ := (kToFrac K e n).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval]
  change Function.Injective (eval₂Hom (kToFrac K e n) (parYF K e n))
  let M : Submonoid (MvPolynomial (Par e n) (𝓞 K)) := (nonZeroDivisors (𝓞 K)).map C
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M z
  have h := IsLocalization.mk'_spec (MvPolynomial (Par e n) K) a s
  have hc := eval_parYF_comp K e n
  have ha : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) a = 0 := by
    rw [← hc, RingHom.comp_apply, ← h, map_mul, hz, zero_mul]
  have ha0 : a = 0 := IsFractionRing.injective _ _ (ha.trans (map_zero _).symm)
  subst ha0
  exact IsLocalization.mk'_zero _

end

end GroundTheory.Heights₂.Heights.Vertical
