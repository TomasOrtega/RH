import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.ApproxHatO

/- English proof (translation)
Introduce `E _ _ _ c hc y z`. Use `set N : ℕ := Ideal.absNorm c with hNdef`. Establish `hN : N ≠ 0` using `by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]`. Establish `hNc : (N : OF E) ∈ c` using `Ideal.absNorm_mem c`. Establish `hNE : (N : E) ≠ 0` using `Nat.cast_ne_zero.mpr hN`.

Use `set u : Af E := algebraMap E (Af E) (N : E)⁻¹ with hu`. Use `set U : Set (Af E) := {a | ∀ v, (u * a * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E} with hU`. Establish `hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E}` using `RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) fun _ => Valued.isOpen_valuationSubring _`. Establish `hV : IsOpen {x' : Af E | z - x' ∈ U}` using `hO.preimage (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const))`. Establish `hz : z ∈ {x' : Af E | z - x' ∈ U}` using `by show ∀ v, (u * (z - z) * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E`.

Introduce `v`. Rewrite using `[sub_self, mul_zero, zero_mul]`. Conclude with `zero_mem _`. Take `⟨x, hx⟩` from `GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨z, hz⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Establish `key` using `GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := u * (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E)) hx`. Establish `e : algebraMap E (Af E) (algebraMap (OF E) E (N : OF E)) * u = 1`. Rewrite using `[map_natCast, hu, ← map_mul, mul_inv_cancel₀ hNE, map_one]`. Rewrite `key` using `[← mul_assoc, ← mul_assoc, e, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_sub_mul_mem_hatO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro E _ _ _ c hc y z
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set u : Af E := algebraMap E (Af E) (N : E)⁻¹ with hu
  set U : Set (Af E) := {a | ∀ v, (u * a * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E} with hU
  have hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      fun _ => Valued.isOpen_valuationSubring _
  have hV : IsOpen {x' : Af E | z - x' ∈ U} :=
    hO.preimage (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const))
  have hz : z ∈ {x' : Af E | z - x' ∈ U} := by
    show ∀ v, (u * (z - z) * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E
    intro v
    rw [sub_self, mul_zero, zero_mul]
    exact zero_mem _
  obtain ⟨x, hx⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨z, hz⟩
  refine ⟨x, ?_⟩
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := u * (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E)) hx
  have e : algebraMap E (Af E) (algebraMap (OF E) E (N : OF E)) * u = 1 := by
    rw [map_natCast, hu, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  rwa [← mul_assoc, ← mul_assoc, e, one_mul] at key

end GlobalTheory.CMVal.ApproxHatO
