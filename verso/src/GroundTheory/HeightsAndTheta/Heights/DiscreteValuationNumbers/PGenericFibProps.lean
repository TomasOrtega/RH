import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem weightedHomogeneousComponent_map {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ P hP hT`. Use `set φ := algebraMap O (FractionRing O) with hφ`. Set `M : Submonoid (MRing ι O)` to `(nonZeroDivisors O).map (C (σ := Σ k, ι k))`. Establish `: IsLocalization M (MRing ι (FractionRing O))` using `MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)`. Establish `hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ` using `rfl`.

Establish `hdisj : Disjoint (M : Set (MRing ι O)) P`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨m, hm, rfl⟩ hmP`. Establish `: m ∈ P.comap (C : O →+* MRing ι O)` using `hmP`. Rewrite `this` using `[hT, Ideal.mem_bot]`.

Conclude with `nonZeroDivisors.ne_zero hm this`. Establish `hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P` using `rfl`. Establish `hprime : (genFib P).IsPrime` using `hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj`. Establish `hunder : (genFib P).comap (MvPolynomial.map φ) = P` using `IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj`. Use `⟨hprime, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx b`. Rewrite `hx` using `[hgen, IsLocalization.mem_map_algebraMap_iff M]`. Take `⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩` from `hx`. Simplify using `only [hmap, map_C] at h`. Establish `hm0 : φ m ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm`.

Establish `hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p`. Rewrite using `[← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]`. Rewrite using `[hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))`. Introduce `s c hs hsP`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Apply `hs` to reduce the goal to its premises. Introduce `h0`. Rewrite `hd` using `[coeff_map, h0, map_zero]`.

Conclude with `hd rfl`. Introduce `h`. Apply `hsP` to reduce the goal to its premises. Rewrite using `[← hunder]`. Conclude with `h`.
-/
theorem GenericFibProps.proof : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
