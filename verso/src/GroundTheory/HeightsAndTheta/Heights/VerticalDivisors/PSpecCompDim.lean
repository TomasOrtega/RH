import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCompDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [coeff_homogeneousComponent, coeff_map]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem homogeneousComponent_map_coeffs {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/- English proof (translation)
Introduce `K _ _ n e I f v hI hf W hW`. Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Establish `: I.IsPrime` using `hI.isPrime`. Set `k` to `v.asIdeal.ResidueField`. Set `φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k` to `MvPolynomial.map (algebraMap (𝓞 K) k)`.

Set `ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K` to `MvPolynomial.map (algebraMap (𝓞 K) K)`. Establish `hφ : Function.Surjective φ` using `MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)`. Establish `hker : RingHom.ker φ = Ideal.map C v.asIdeal`. Rewrite using `[MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]`. Take `⟨hWmin, hWrel⟩` from `hW`.

Establish `hWprime : W.IsPrime` using `hWmin.1.1`. Establish `hkerW : RingHom.ker φ ≤ W` using `hker ▸ le_sup_right.trans hWmin.1.2`. Establish `hP : (integralModel I).IsPrime` using `Ideal.comap_isPrime ψ I`. Establish `hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥`. Use extensionality with `c`.

Simplify using `only [Ideal.mem_comap, integralModel, Ideal.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Establish `hu : IsUnit (ψ (C c))`.

Rewrite using `[show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]`. Conclude with `(isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C`. Conclude with `hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules.

Establish `hPloc : (integralModel I).map ψ = I`. Set `_` to `MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)`. Use `MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K` as an intermediate fact. Conclude with `IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n))) (MvPolynomial (Fin n) K) I`. Establish `hdim` using `hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin`.

Rewrite `hdim` using `[hPloc, hCone K n (e + 1) I f hI hf]`. Use `⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩` and prove the remaining obligations. Establish `hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes`. Express the relevant statement in the definitionally equal form `W.map φ ∈ ((integralModel I).map φ).minimalPrimes`. Rewrite using `[Ideal.minimalPrimes_map_of_surjective hφ, hker]`.

Conclude with `⟨W, hWmin, rfl⟩`. Use `MinimalPrimeHomog.proof k n _ _ ?_ hmin` and prove the remaining obligations. Introduce `g hg d`. Express the relevant statement in the definitionally equal form `g ∈ (integralModel I).map φ at hg`. Take `⟨p, hp, rfl⟩` from `(Ideal.mem_map_iff_of_surjective φ hφ).mp hg`.

Rewrite using `[homogeneousComponent_map_coeffs]`. Use `Ideal.mem_map_of_mem φ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (homogeneousComponent d p) ∈ I`. Rewrite using `[← homogeneousComponent_map_coeffs]`. Conclude with `hI.isHomog _ hp d`.

Take `⟨j, hj⟩` from `hWrel`. Use `⟨j, fun h => hj ?_⟩` and prove the remaining obligations. Establish `h' : X j ∈ (W.map φ).comap φ`. Rewrite using `[Ideal.mem_comap, map_X]`. Conclude with `h`.

Rewrite `h'` using `[Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerW]`. Then use the resulting hypothesis.
-/
theorem SpecCompDim.proof (hCone : ConeDimOfChowForm.Statement) (hFib : FibreCompDim.Statement) :
    SpecCompDim.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : I.IsPrime := hI.isPrime
  let k := v.asIdeal.ResidueField
  let φ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (𝓞 K) k)
  let ψ : MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) K :=
    MvPolynomial.map (algebraMap (𝓞 K) K)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hker : RingHom.ker φ = Ideal.map C v.asIdeal := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWprime : W.IsPrime := hWmin.1.1
  have hkerW : RingHom.ker φ ≤ W := hker ▸ le_sup_right.trans hWmin.1.2

  have hP : (integralModel I).IsPrime := Ideal.comap_isPrime ψ I
  have hPC : (integralModel I).comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, integralModel, Ideal.mem_bot]
    constructor
    · intro h
      by_contra hc
      have hu : IsUnit (ψ (C c)) := by
        rw [show ψ (C c) = C (algebraMap (𝓞 K) K c) from map_C _ _]
        exact (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hc)).map C
      exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    · rintro rfl
      simp
  have hPloc : (integralModel I).map ψ = I := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := 𝓞 K) (S := K)
    have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (𝓞 K)) K
    exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin n)))
      (MvPolynomial (Fin n) K) I
  have hdim := hFib (𝓞 K) K n (integralModel I) W v hP hPC hWmin
  rw [hPloc, hCone K n (e + 1) I f hI hf] at hdim
  refine ⟨⟨Ideal.map_isPrime_of_surjective hφ hkerW, ?_, ?_⟩, hdim⟩
  ·
    have hmin : reduceMod v W ∈ (reduceMod v (integralModel I)).minimalPrimes := by
      change W.map φ ∈ ((integralModel I).map φ).minimalPrimes
      rw [Ideal.minimalPrimes_map_of_surjective hφ, hker]
      exact ⟨W, hWmin, rfl⟩
    refine MinimalPrimeHomog.proof k n _ _ ?_ hmin
    intro g hg d
    change g ∈ (integralModel I).map φ at hg
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hg
    rw [homogeneousComponent_map_coeffs]
    refine Ideal.mem_map_of_mem φ ?_
    change ψ (homogeneousComponent d p) ∈ I
    rw [← homogeneousComponent_map_coeffs]
    exact hI.isHomog _ hp d
  ·
    obtain ⟨j, hj⟩ := hWrel
    refine ⟨j, fun h => hj ?_⟩
    have h' : X j ∈ (W.map φ).comap φ := by
      rw [Ideal.mem_comap, map_X]
      exact h
    rwa [Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerW] at h'

end

end GroundTheory.Heights₂.Heights.Vertical
