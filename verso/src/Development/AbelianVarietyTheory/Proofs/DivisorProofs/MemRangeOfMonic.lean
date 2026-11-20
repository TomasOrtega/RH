import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero

open Polynomial

namespace GlobalTheory.MonicRootRange

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_` and prove the remaining obligations. Take `⟨b, hb, hq⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors T) p`. Use `set q := IsLocalization.integerNormalization (nonZeroDivisors T) p`. Use `set f := algebraMap T (FractionRing T)`. Establish `hinj : Function.Injective f` using `IsFractionRing.injective T (FractionRing T)`.

Establish `hb0 : f b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p`. Rewrite using `[Algebra.smul_def, Polynomial.algebraMap_apply]`. Establish `hn : 1 ≤ p.natDegree` using `natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)`. Establish `hdeg : q.natDegree = p.natDegree`.

Use `congrArg natDegree hq` as an intermediate fact. Rewrite `this` using `[natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0]`. Then use the resulting hypothesis. Establish `hq0 : q ≠ 0` using `fun h0 => by rw [h0, natDegree_zero] at hdeg; omega`. Establish `hc0 : f q.leadingCoeff ≠ 0` using `(map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)`. Take `⟨w, hw⟩` from `h q.integralNormalization (monic_integralNormalization hq0) (by rw [natDegree_integralNormalization]; omega)`.

Use `⟨f w / f q.leadingCoeff, ?_⟩` and prove the remaining obligations. Establish `key` using `integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)`. Rewrite `key` using `[mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero]`. Establish `h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0` using `(mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)`. Rewrite `h2` using `[← eval_map, hq, hsmul, eval_mul, eval_C]`.

Conclude with `(mul_eq_zero.mp h2).resolve_left hb0`.
-/
theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
