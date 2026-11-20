import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.LocalNormNegOne

open Polynomial IsLocalRing

/- English proof (translation)
Use `Fintype.ofFinite k` as an intermediate fact. Establish `hc : ringChar k ≠ 2` using `fun h => h2 (by`. Use `ringChar.Nat.cast_ringChar (R := k)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this)` after adjusting the coercions.

Establish `hodd : Fintype.card k % 2 = 1` using `FiniteField.odd_card_of_char_ne_two hc`. Take `⟨x, y, h⟩` from `FiniteField.exists_root_sum_quadratic (R := k) (f := X ^ 2) (g := C (-D) * X ^ 2 + C 0 * X + C 4) (degree_X_pow 2) (degree_quadratic (neg_ne_zero.2 hD)) hodd`. Use `⟨x, y, ?_⟩` and prove the remaining obligations. Simplify using `only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at h`. Take the linear combination `h`.
-/
theorem exists_sq_sub_finite {k : Type*} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ x y : k, x ^ 2 - (D * y ^ 2 - 4) = 0 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this)
  have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic (R := k) (f := X ^ 2)
    (g := C (-D) * X ^ 2 + C 0 * X + C 4) (degree_X_pow 2) (degree_quadratic (neg_ne_zero.2 hD)) hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at h
  linear_combination h

variable {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `HenselianRing.is_henselian (I := maximalIdeal R) (X ^ 2 + C p * X + C q) (by monicity!) x₀ (by simpa using h₀) (by`. Establish `: (X ^ 2 + C p * X + C q : R[X]).derivative.eval x₀ = 2 * x₀ + p`. Simplify using `[one_add_one_eq_two]`. Rewrite using `[this]`. Conclude with `h₁.map _)`.

Conclude with `⟨x, by simpa [IsRoot] using hx, hx'⟩`.
-/
theorem exists_root_quadratic (p q x₀ : R) (h₀ : x₀ ^ 2 + p * x₀ + q ∈ maximalIdeal R)
    (h₁ : IsUnit (2 * x₀ + p)) : ∃ x : R, x ^ 2 + p * x + q = 0 ∧ x - x₀ ∈ maximalIdeal R := by
  obtain ⟨x, hx, hx'⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ 2 + C p * X + C q) (by monicity!) x₀ (by simpa using h₀) (by
      have : (X ^ 2 + C p * X + C q : R[X]).derivative.eval x₀ = 2 * x₀ + p := by
        simp [one_add_one_eq_two]
      rw [this]
      exact h₁.map _)
  exact ⟨x, by simpa [IsRoot] using hx, hx'⟩

/- English proof (translation)
Distinguish the cases in `h2 : IsUnit (2 : R)`. Take `⟨u, hu⟩` from `h2.exists_left_inv`. Establish `key : ∃ x b : R, x ^ 2 - ((t ^ 2 - 4 * n) * b ^ 2 - 4) = 0`. Generalize the expression as in `t ^ 2 - 4 * n = D at hD`. Take `⟨x, y, h⟩` from `exists_sq_sub_finite (k := ResidueField R) (by have := (h2.map (residue R)).ne_zero; rwa [map_ofNat] at this) (residue R D) (hD.map _).ne_zero`.

Take `⟨x, rfl⟩` from `residue_surjective x`. Take `⟨y, rfl⟩` from `residue_surjective y`. Establish `hm : x ^ 2 - (D * y ^ 2 - 4) ∈ maximalIdeal R`. Rewrite using `[← residue_eq_zero_iff, ← h]`. Simplify using `[map_ofNat]`.

Distinguish the cases in `hx : IsUnit x`. Take `⟨z, hz, -⟩` from `exists_root_quadratic 0 (-(D * y ^ 2 - 4)) x (by simpa [sub_eq_add_neg] using hm) (by simpa using h2.mul hx)`. Conclude with `⟨z, y, by linear_combination hz⟩`. Establish `hxm : x ∈ maximalIdeal R` using `hx`. Establish `hm' : D * y ^ 2 - 4 ∈ maximalIdeal R`.

Use `(maximalIdeal R).sub_mem (Ideal.mul_mem_left _ x hxm) hm` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd⟩` from `hD.exists_left_inv`. Establish `hy : IsUnit y`.

Assume the negation of the conclusion as `hy`. Establish `hym : y ∈ maximalIdeal R` using `hy`. Establish `h4 : (2 * 2 : R) ∈ maximalIdeal R`. Use `(maximalIdeal R).sub_mem (Ideal.mul_mem_left _ (D * y) hym) hm'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h4 (h2.mul h2)`. Take `⟨z, hz, -⟩` from `exists_root_quadratic 0 (-(4 * d)) y (by`. Use `Ideal.mul_mem_left _ d hm'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Take the linear combination `(-y ^ 2) * hd) (by simpa using h2.mul hy)`. Conclude with `⟨0, z, by linear_combination (-D) * hz - 4 * hd⟩`. Take `⟨x, b, h⟩` from `key`. Use `⟨u * (x - t * b), b, ?_⟩` and prove the remaining obligations. Take the linear combination `u ^ 2 * h - (u * (x - t * b) * b * t + (b ^ 2 * n + 1) * (u * 2 + 1)) * hu`.

Establish `h2m : (2 : R) ∈ maximalIdeal R` using `h2`. Establish `ht : IsUnit t`. Assume the negation of the conclusion as `ht`. Establish `htm : t ∈ maximalIdeal R` using `ht`. Establish `: t ^ 2 - 4 * n ∈ maximalIdeal R`.

Use `(maximalIdeal R).sub_mem (Ideal.mul_mem_left _ t htm) (Ideal.mul_mem_left _ (2 * n) h2m)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `this hD`. Take `⟨c, hc, hc'⟩` from `exists_root_quadratic t (2 * n) (-t) (by`.

Use `Ideal.mul_mem_left _ n h2m` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Use the proof step `(by`. Establish `: 2 * -t + t = -t` using `by ring`.

Rewrite using `[this]`. Conclude with `ht.neg)`. Establish `hcu : IsUnit c`. Assume the negation of the conclusion as `hcu`. Establish `hcm : c ∈ maximalIdeal R` using `hcu`.

Establish `: t ∈ maximalIdeal R`. Use `(maximalIdeal R).sub_mem hc' hcm` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `this ht`.

Take `⟨e, he⟩` from `hcu.exists_left_inv`. Use `⟨1, 2 * e, ?_⟩` and prove the remaining obligations. Take the linear combination `2 * e ^ 2 * hc - (2 * e * t + 2 * (e * c + 1)) * he`.
-/
theorem exists_eq_neg_one [Finite (ResidueField R)] (t n : R) (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ a b : R, a ^ 2 + a * b * t + b ^ 2 * n = -1 := by
  by_cases h2 : IsUnit (2 : R)
  · obtain ⟨u, hu⟩ := h2.exists_left_inv
    have key : ∃ x b : R, x ^ 2 - ((t ^ 2 - 4 * n) * b ^ 2 - 4) = 0 := by
      generalize t ^ 2 - 4 * n = D at hD
      obtain ⟨x, y, h⟩ := exists_sq_sub_finite (k := ResidueField R)
        (by have := (h2.map (residue R)).ne_zero; rwa [map_ofNat] at this) (residue R D) (hD.map _).ne_zero
      obtain ⟨x, rfl⟩ := residue_surjective x
      obtain ⟨y, rfl⟩ := residue_surjective y
      have hm : x ^ 2 - (D * y ^ 2 - 4) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, ← h]
        simp [map_ofNat]
      by_cases hx : IsUnit x
      · obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(D * y ^ 2 - 4)) x
          (by simpa [sub_eq_add_neg] using hm) (by simpa using h2.mul hx)
        exact ⟨z, y, by linear_combination hz⟩
      · have hxm : x ∈ maximalIdeal R := hx
        have hm' : D * y ^ 2 - 4 ∈ maximalIdeal R := by
          have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ x hxm) hm
          convert this using 1; ring
        obtain ⟨d, hd⟩ := hD.exists_left_inv
        have hy : IsUnit y := by
          by_contra hy
          have hym : y ∈ maximalIdeal R := hy
          have h4 : (2 * 2 : R) ∈ maximalIdeal R := by
            have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ (D * y) hym) hm'
            convert this using 1; ring
          exact h4 (h2.mul h2)
        obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(4 * d)) y
          (by
            have := Ideal.mul_mem_left _ d hm'
            convert this using 1
            linear_combination (-y ^ 2) * hd) (by simpa using h2.mul hy)
        exact ⟨0, z, by linear_combination (-D) * hz - 4 * hd⟩
    obtain ⟨x, b, h⟩ := key
    refine ⟨u * (x - t * b), b, ?_⟩
    linear_combination u ^ 2 * h
      - (u * (x - t * b) * b * t + (b ^ 2 * n + 1) * (u * 2 + 1)) * hu
  · have h2m : (2 : R) ∈ maximalIdeal R := h2
    have ht : IsUnit t := by
      by_contra ht
      have htm : t ∈ maximalIdeal R := ht
      have : t ^ 2 - 4 * n ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ t htm) (Ideal.mul_mem_left _ (2 * n) h2m)
        convert this using 1; ring
      exact this hD
    obtain ⟨c, hc, hc'⟩ := exists_root_quadratic t (2 * n) (-t)
      (by
        have := Ideal.mul_mem_left _ n h2m
        convert this using 1; ring)
      (by
        have : 2 * -t + t = -t := by ring
        rw [this]; exact ht.neg)
    have hcu : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ maximalIdeal R := hcu
      have : t ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem hc' hcm
        convert this using 1; ring
      exact this ht
    obtain ⟨e, he⟩ := hcu.exists_left_inv
    refine ⟨1, 2 * e, ?_⟩
    linear_combination 2 * e ^ 2 * hc - (2 * e * t + 2 * (e * c + 1)) * he

/- English proof (translation)
Introduce and unpack `F E _ _ _ _ _ _ - v θ ⟨t, n, h1, h2, h3⟩`. Use `GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v` as an intermediate fact. Use `GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v` as an intermediate fact. Establish `hD` using `(GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3`. Rewrite `hD` using `[map_sub, map_pow, map_mul, map_ofNat]`.

Take `⟨a, b, h⟩` from `exists_eq_neg_one _ _ hD`. Conclude with `⟨a, b, t, n, h1, h2, h⟩`.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E), (∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ v.asIdeal) → ∃ a b : v.adicCompletionIntegers F, ∃ t n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t + b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 := by
  rintro F E _ _ _ _ _ _ - v θ ⟨t, n, h1, h2, h3⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hD := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
  rw [map_sub, map_pow, map_mul, map_ofNat] at hD
  obtain ⟨a, b, h⟩ := exists_eq_neg_one _ _ hD
  exact ⟨a, b, t, n, h1, h2, h⟩

end GlobalTheory.LocalNormNegOne
