import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

/- English proof (translation)
Introduce `K _ _ v σ f hf`. Use `set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m) with hJdef`. Establish `hJ : J ≠ 0`. Rewrite using `[hJdef, FractionalIdeal.spanFinset_ne_zero]`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.mp hf`.

Conclude with `⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩`. Establish `hJJ : J * J⁻¹ = 1` using `mul_inv_cancel₀ hJ`. Establish `hcoeff : ∀ m, f.coeff m ∈ J`. Introduce `m`. Distinguish the cases in `hm : f.coeff m = 0`.

Rewrite using `[hm, ← FractionalIdeal.mem_coe]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]`. Conclude with `Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩`. Establish `hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m`.

Introduce `c hc m`. Establish `h1 : f.coeff m * c ∈ J * J⁻¹` using `FractionalIdeal.mul_mem_mul (hcoeff m) hc`. Rewrite `h1` using `[hJJ, FractionalIdeal.mem_one_iff]`. Take `⟨y, hy⟩` from `h1`. Conclude with `⟨y, by rw [hy, mul_comm]⟩`.

Establish `hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Set `S : Submodule (𝓞 K) K` to `Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal`. Establish `hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S`.

Rewrite using `[FractionalIdeal.coe_mul, Submodule.mul_le]`. Introduce `j hj c hc`. Establish `hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c)`. Rewrite using `[hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]`. Introduce and unpack `_ ⟨m, -, rfl⟩`.

Take `⟨y, hy⟩` from `hint c hc m`. Use `Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.linearMap_apply, LinearMap.mulRight_apply]`. Rewrite using `[hy, mul_comm]`. Conclude with `hJS hj`.

Establish `h1 : (1 : K) ∈ S`. Apply `hle` to reduce the goal to its premises. Rewrite using `[hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]`. Conclude with `⟨1, map_one _⟩`. Take `⟨y, hy, hy1⟩` from `Submodule.mem_map.mp h1`.

Establish `: y = 1`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Simplify using `using hy1`. Rewrite `hy` using `[this]`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)`.

Take `⟨c, hc, m0, y0, hy0, hy0v⟩` from `hex`. Establish `hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K)`. Introduce `a ha`. Take `⟨m, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp ha`. Take `⟨y, hy⟩` from `hint c hc m`.

Conclude with `⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩`. Take `⟨g, hg⟩` from `MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Apply `hy0v` to reduce the goal to its premises.

Establish `: algebraMap (𝓞 K) K y0 = 0` using `by rw [hy0, zero_mul]`. Rewrite using `[(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]`. Conclude with `zero_mem _`. Use `⟨c, g, hc0, hg, m0, ?_⟩` and prove the remaining obligations. Establish `hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0`.

Rewrite using `[hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]`. Rewrite using `[(IsFractionRing.injective (𝓞 K) K) hgm]` and apply the resulting hypothesis.
-/
theorem PrimitiveScale.proof : PrimitiveScale.Statement := by
  intro K _ _ v σ f hf
  classical
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m)
    with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, FractionalIdeal.spanFinset_ne_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  have hcoeff : ∀ m, f.coeff m ∈ J := by
    intro m
    by_cases hm : f.coeff m = 0
    · rw [hm, ← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _
    · rw [← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]
      exact Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m := by
    intro c hc m
    have h1 : f.coeff m * c ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul (hcoeff m) hc
    rw [hJJ, FractionalIdeal.mem_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [hy, mul_comm]⟩

  have hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal := by
    by_contra hne
    push Not at hne
    let S : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal
    have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro j hj c hc
      have hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c) := by
        rw [hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]
        rintro _ ⟨m, -, rfl⟩
        obtain ⟨y, hy⟩ := hint c hc m
        refine Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩
        simp only [Algebra.linearMap_apply, LinearMap.mulRight_apply]
        rw [hy, mul_comm]
      exact hJS hj
    have h1 : (1 : K) ∈ S := by
      apply hle
      rw [hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    obtain ⟨y, hy, hy1⟩ := Submodule.mem_map.mp h1
    have : y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      simpa using hy1
    rw [this] at hy
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)
  obtain ⟨c, hc, m0, y0, hy0, hy0v⟩ := hex
  have hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K) := by
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    obtain ⟨y, hy⟩ := hint c hc m
    exact ⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩
  obtain ⟨g, hg⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0v
    have : algebraMap (𝓞 K) K y0 = 0 := by rw [hy0, zero_mul]
    rw [(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨c, g, hc0, hg, m0, ?_⟩
  have hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0 := by
    rw [hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]
  rwa [(IsFractionRing.injective (𝓞 K) K) hgm]

end

end GroundTheory.Heights₂.Heights.Vertical
