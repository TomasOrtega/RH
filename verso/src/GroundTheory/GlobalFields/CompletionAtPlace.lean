import Mathlib
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.Interface

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped WithZero

namespace GroundTheory.Global

section Map

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

def adicCompletionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

/- English proof (translation)
The claim follows from `(adicCompletion.continuous_ofCompletion L w).comp <| UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)`.
-/
theorem continuous_adicCompletionMap : Continuous (adicCompletionMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

/- English proof (translation)
Apply `adicCompletion.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `UniformSpace.Completion.mapRingHom _ (uniformContinuous_algebraMap_liesOver K L v w).continuous ((algebraMap K (WithVal (v.valuation K)) x : WithVal (v.valuation K)) : UniformSpace.Completion (WithVal (v.valuation K))) = _`. Rewrite using `[UniformSpace.Completion.mapRingHom_coe]`. Both sides reduce to the same expression.
-/
theorem adicCompletionMap_algebraMap (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_algebraMap_liesOver K L v w).continuous
    ((algebraMap K (WithVal (v.valuation K)) x : WithVal (v.valuation K)) :
      UniformSpace.Completion (WithVal (v.valuation K))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

end Map

namespace AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionMap v w).toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_eq : algebraMap (v.adicCompletion K) (w.adicCompletion L) =
    adicCompletionMap v w :=
  rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_eq, adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L]

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_adicCompletionMap v w)

end AdicLiesOver

section Extension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

/- English proof (translation)
Establish `h` using `(denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)) (continuous_adicCompletionMap v w) (funext fun x ↦ ?_)`. Conclude with `RingHom.ext (congrFun h)`. Simplify using `only [Function.comp_apply]`. Rewrite using `[adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]`.
-/
theorem algebraMap_adicCompletion_eq [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = adicCompletionMap v w := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L))
    (continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]

/- English proof (translation)
Establish `he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `[he]`. Establish `hx' : Valued.v x ≠ 0` using `by simpa using hx`. Establish `hy : Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) ≠ 0`.

Simplify using `using hx`. Establish `h1` using `Valued.locally_const hx'`. Establish `h2` using `(continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).continuousAt.preimage_mem_nhds (Valued.locally_const hy)`. Take `⟨k, hk1, hk2⟩` from `(denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds (Filter.inter_mem h1 h2)`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2`.

Rewrite using `[← hk1, ← hk2, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]`. Use `erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]`. Conclude with `(valuation_liesOver L v w k).symm`.
-/
theorem valued_algebraMap_adicCompletion' [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy : Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) ≠ 0 := by
    simpa using hx
  have h1 := Valued.locally_const hx'
  have h2 := (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).continuousAt.preimage_mem_nhds
    (Valued.locally_const hy)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]
  exact (valuation_liesOver L v w k).symm

/- English proof (translation)
Rewrite using `[valued_algebraMap_adicCompletion', Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]`.
-/
theorem valued_algebraMap_adicCompletion [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  rw [valued_algebraMap_adicCompletion',
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]

instance valuativeExtension_adicCompletion [w.asIdeal.LiesOver v.asIdeal] :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)),
      valued_algebraMap_adicCompletion', valued_algebraMap_adicCompletion']
    exact pow_le_pow_iff_left₀ zero_le zero_le he

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem finite_adicCompletion : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

end Extension

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := inferInstance

end Check

end GroundTheory.Global
