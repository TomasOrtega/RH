import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.UnramTraceDenom

/- English proof (translation)
Introduce `F E _ _ _ _ _ hU v e h`. Use `haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hU`. Use `haveI := v.isPrime`. Set `b` to `NumberField.RingOfIntegers.basis E`. Establish `hloc : ∀ i, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F s * Algebra.trace F E ((b i : E) * e) = algebraMap (𝓞 F) F r`.

Introduce `i`. Apply `GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem` to reduce the goal to its premises. Establish `hi` using `h (b i)`. Rewrite `hi` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e1` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Algebra.trace F E ((b i : E) * e))`.

Conclude with `e1 ▸ hi`. Use `choose s hs r hr using hloc`. Use `⟨∏ i, s i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨i, -, hi⟩`.

Conclude with `hs i hi`. Establish `key : ∀ i, algebraMap (𝓞 F) F (∏ j, s j) * Algebra.trace F E ((b i : E) * e) ∈ (algebraMap (𝓞 F) F).range`. Introduce `i`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap (𝓞 F) F (s i)), mul_assoc, hr i, ← map_mul]`. Conclude with `⟨_, rfl⟩`.

Establish `htr : ∀ a : 𝓞 E, Algebra.trace F E (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * a) ∈ (algebraMap (𝓞 F) F).range`. Introduce `a`. Establish `ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : E) * (b i : E)`. Use `congrArg (algebraMap (𝓞 E) E) (b.sum_repr a)` as an intermediate fact. Simplify `this.symm` using `[map_sum, zsmul_eq_mul]`.

Rewrite using `[ha, Finset.mul_sum, map_sum]`. Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `e2 : algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * (((b.repr a i : ℤ) : E) * (b i : E)) = algebraMap F E (((b.repr a i : ℤ) : F) * algebraMap (𝓞 F) F (∏ j, s j)) * ((b i : E) * e)`. Establish `hc : ((∏ i, s i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∏ j, s j)` using `rfl`. Rewrite using `[hc, map_mul, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_assoc]`. Conclude with `Subring.mul_mem _ (intCast_mem _ _) (key i)`. Take `⟨y, hy⟩` from `GlobalTheory.InertSelfDual.mem_of_trace (F := F) (E := E) (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e) htr`. Rewrite using `[← hy]`.

Conclude with `RingOfIntegers.isIntegral_coe y`.
-/
theorem exists_not_mem_mul_isIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl F) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  intro F E _ _ _ _ _ hU v e h
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hU
  haveI := v.isPrime
  let b := NumberField.RingOfIntegers.basis E
  have hloc : ∀ i, ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F s * Algebra.trace F E ((b i : E) * e) = algebraMap (𝓞 F) F r := by
    intro i
    apply GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
    have hi := h (b i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hi
    have e1 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (Algebra.trace F E ((b i : E) * e))
    exact e1 ▸ hi
  choose s hs r hr using hloc
  refine ⟨∏ i, s i, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hs i hi
  · have key : ∀ i, algebraMap (𝓞 F) F (∏ j, s j) * Algebra.trace F E ((b i : E) * e) ∈
        (algebraMap (𝓞 F) F).range := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap (𝓞 F) F (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    have htr : ∀ a : 𝓞 E, Algebra.trace F E (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * a) ∈
        (algebraMap (𝓞 F) F).range := by
      intro a
      have ha : (a : E) = ∑ i, ((b.repr a i : ℤ) : E) * (b i : E) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr a)
        simpa [map_sum, zsmul_eq_mul] using this.symm
      rw [ha, Finset.mul_sum, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      have e2 : algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e * (((b.repr a i : ℤ) : E) * (b i : E)) =
          algebraMap F E (((b.repr a i : ℤ) : F) * algebraMap (𝓞 F) F (∏ j, s j)) * ((b i : E) * e) := by
        have hc : ((∏ i, s i : 𝓞 F) : F) = algebraMap (𝓞 F) F (∏ j, s j) := rfl
        rw [hc, map_mul, map_intCast]; ring
      rw [e2, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_assoc]
      exact Subring.mul_mem _ (intCast_mem _ _) (key i)
    obtain ⟨y, hy⟩ := GlobalTheory.InertSelfDual.mem_of_trace (F := F) (E := E)
      (algebraMap F E ((∏ i, s i : 𝓞 F) : F) * e) htr
    rw [← hy]; exact RingOfIntegers.isIntegral_coe y

end GlobalTheory.UnramTraceDenom
