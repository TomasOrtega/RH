import Mathlib

namespace GlobalTheory.CompanionTheory.IntegralClosureLocal

/- English proof (translation)
Set `f : R →+* (integralClosure R K).toSubring` to `(algebraMap R K).codRestrict (integralClosure R K).toSubring (fun r => (integralClosure R K).algebraMap_mem r)`. Use `letI : Algebra R (integralClosure R K).toSubring := f.toAlgebra`. Use `haveI : Algebra.IsIntegral R (integralClosure R K).toSubring := by`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, h⟩ : IsIntegral R (x : K)` from `x.2`.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Establish `key` using `Polynomial.hom_eval₂ p f (integralClosure R K).toSubring.subtype x`. Conclude with `key.trans h`. Establish `hm : (P.comap (algebraMap R (integralClosure R K).toSubring)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`.

Establish `hmax : P.comap (algebraMap R (integralClosure R K).toSubring) = IsLocalRing.maximalIdeal R` using `IsLocalRing.eq_maximalIdeal hm`. Establish `hrt : algebraMap R (integralClosure R K).toSubring ⟨t, htR⟩ = t` using `Subtype.ext rfl`. Establish `h1 : t ∈ P ↔ (⟨t, htR⟩ : R) ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[← hmax, Ideal.mem_comap, hrt]`. Rewrite using `[h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]`.

Prove the components needed by the constructor for the conclusion. Introduce `hu`. Take `⟨u, hu⟩` from `hu`. Establish `hne : (t : K) ≠ 0`. Introduce `h0`.

Establish `: (u : R) = 0` using `by rw [hu]; exact Subtype.ext h0`. Conclude with `u.ne_zero this`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Establish `hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv, Subring.coe_one]`.

Establish `hut : ((u : R) : K) = (t : K)` using `by rw [hu]`. Rewrite `hmul` using `[hut]`. Establish `: (t : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K)` using `inv_eq_of_mul_eq_one_right hmul`. Rewrite using `[this]`. Conclude with `Subtype.coe_prop _`.

Introduce and unpack `⟨hne, hinv⟩`. Use `IsUnit.of_mul_eq_one (⟨(t : K)⁻¹, hinv⟩ : R) ?_` and prove the remaining obligations. Conclude with `Subtype.ext (mul_inv_cancel₀ hne)`.
-/
theorem mem_maximal_iff_not_inv_mem {K : Type} [Field K] (R : Subring K) [IsLocalRing R]
    (P : Ideal (integralClosure R K).toSubring) (hP : P.IsMaximal)
    (t : (integralClosure R K).toSubring) (htR : (t : K) ∈ R) :
    t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R) := by
  let f : R →+* (integralClosure R K).toSubring :=
    (algebraMap R K).codRestrict (integralClosure R K).toSubring
      (fun r => (integralClosure R K).algebraMap_mem r)
  letI : Algebra R (integralClosure R K).toSubring := f.toAlgebra
  haveI : Algebra.IsIntegral R (integralClosure R K).toSubring := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp, h⟩ : IsIntegral R (x : K) := x.2
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ p f (integralClosure R K).toSubring.subtype x
    exact key.trans h
  have hm : (P.comap (algebraMap R (integralClosure R K).toSubring)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hmax : P.comap (algebraMap R (integralClosure R K).toSubring)
      = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  have hrt : algebraMap R (integralClosure R K).toSubring ⟨t, htR⟩ = t := Subtype.ext rfl
  have h1 : t ∈ P ↔ (⟨t, htR⟩ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hmax, Ideal.mem_comap, hrt]
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hne : (t : K) ≠ 0 := by
      intro h0
      have : (u : R) = 0 := by rw [hu]; exact Subtype.ext h0
      exact u.ne_zero this
    refine ⟨hne, ?_⟩
    have hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hut : ((u : R) : K) = (t : K) := by rw [hu]
    rw [hut] at hmul
    have : (t : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K) := inv_eq_of_mul_eq_one_right hmul
    rw [this]
    exact Subtype.coe_prop _
  · rintro ⟨hne, hinv⟩
    refine IsUnit.of_mul_eq_one (⟨(t : K)⁻¹, hinv⟩ : R) ?_
    exact Subtype.ext (mul_inv_cancel₀ hne)

end GlobalTheory.CompanionTheory.IntegralClosureLocal
