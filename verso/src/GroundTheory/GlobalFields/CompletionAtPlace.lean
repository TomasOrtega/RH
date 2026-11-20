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
A detailed English derivation is pending.
-/
theorem continuous_adicCompletionMap : Continuous (adicCompletionMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities.
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
A detailed English derivation is pending.
-/
theorem finite_adicCompletion : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  inferInstance

end Extension

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := inferInstance

end Check

end GroundTheory.Global
