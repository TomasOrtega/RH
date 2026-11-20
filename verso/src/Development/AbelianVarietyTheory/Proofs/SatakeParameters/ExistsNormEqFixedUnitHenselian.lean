import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConjStatement

open Polynomial

namespace GlobalTheory.HenselianNorm

/- English proof (translation)
Take `⟨s, hs, hsI⟩` from `HenselianRing.is_henselian (I := I) (X ^ 2 + X - C (n * e)) (by monicity!) 0 (by`. Simplify using `only [eval_sub, eval_add, eval_pow, eval_X, eval_C]`. Simplify using `using I.mul_mem_left n he)`. Use the proof step `(by simp)`. Establish `h0 : eval s (X ^ 2 + X - C (n * e)) = 0` using `hs`.

Simplify using `only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0`. Rewrite `hsI` using `[sub_zero]`. Take `⟨U, hU⟩` from `(Ideal.mem_jacobson_bot.mp (HenselianRing.jac hsI)) 1`. Establish `hinv : (s + 1) * (↑U⁻¹ : R) = 1`. Rewrite using `[show s + 1 = (U : R) by rw [hU]; ring]`.

Conclude with `U.mul_inv`. Establish `hnt : n * (e * ↑U⁻¹) = s`. Take the linear combination `(-(↑U⁻¹ : R)) * h0 + s * hinv`. Use `⟨e * ↑U⁻¹, I.mul_mem_right _ he, ?_⟩` and prove the remaining obligations. Take the linear combination `(e * ↑U⁻¹) * hnt + e * hinv`.
-/
theorem exists_mem_add_mul_sq_eq {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (n : R) {e : R} (he : e ∈ I) : ∃ t ∈ I, t + n * t ^ 2 = e := by
  obtain ⟨s, hs, hsI⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C (n * e))
    (by monicity!) 0
    (by
      simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
      simpa using I.mul_mem_left n he)
    (by simp)
  have h0 : eval s (X ^ 2 + X - C (n * e)) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0
  rw [sub_zero] at hsI
  obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hsI)) 1
  have hinv : (s + 1) * (↑U⁻¹ : R) = 1 := by
    rw [show s + 1 = (U : R) by rw [hU]; ring]
    exact U.mul_inv
  have hnt : n * (e * ↑U⁻¹) = s := by
    linear_combination (-(↑U⁻¹ : R)) * h0 + s * hinv
  refine ⟨e * ↑U⁻¹, I.mul_mem_right _ he, ?_⟩
  linear_combination (e * ↑U⁻¹) * hnt + e * hinv

/- English proof (translation)
Take `⟨t, htI, ht⟩` from `exists_mem_add_mul_sq_eq I (w * c w) he`. Establish `hct : c t = t`. Establish `h1 : c t + w * c w * c t ^ 2 = e`. Establish `h` using `congrArg c ht`. Simplify using `only [map_add, map_mul, map_pow, hc, hce] at h`.

Take the linear combination `h`. Establish `hm : w * c w * (t + c t) ∈ I` using `I.mul_mem_left _ (I.add_mem htI (hI t htI))`. Take `⟨U, hU⟩` from `(Ideal.mem_jacobson_bot.mp (HenselianRing.jac hm)) 1`. Establish `hz : (t - c t) * (U : R) = 0`. Rewrite using `[hU]`.

Take the linear combination `ht - h1`. Establish `h2` using `(U.isUnit.mul_left_eq_zero).mp hz`. Take the linear combination `-h2`. Use `⟨1 + w * t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_one, map_mul, hct]`.

Take the linear combination `ht + t * hw`.
-/
theorem exists_norm_eq_one_add {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (c : R →+* R) (hc : ∀ x, c (c x) = x) (hI : ∀ x ∈ I, c x ∈ I) {w : R} (hw : w + c w = 1)
    {e : R} (he : e ∈ I) (hce : c e = e) : ∃ x, x * c x = 1 + e := by
  obtain ⟨t, htI, ht⟩ := exists_mem_add_mul_sq_eq I (w * c w) he
  have hct : c t = t := by
    have h1 : c t + w * c w * c t ^ 2 = e := by
      have h := congrArg c ht
      simp only [map_add, map_mul, map_pow, hc, hce] at h
      linear_combination h
    have hm : w * c w * (t + c t) ∈ I := I.mul_mem_left _ (I.add_mem htI (hI t htI))
    obtain ⟨U, hU⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac hm)) 1
    have hz : (t - c t) * (U : R) = 0 := by
      rw [hU]
      linear_combination ht - h1
    have h2 := (U.isUnit.mul_left_eq_zero).mp hz
    linear_combination -h2
  refine ⟨1 + w * t, ?_⟩
  rw [map_add, map_one, map_mul, hct]
  linear_combination ht + t * hw

/- English proof (translation)
Introduce `R _ I _ _ c hc hI hω u hcu hu`. Take `⟨ω, D, hD⟩` from `hω`. Establish `hcD : (c ω - ω) * c ↑D⁻¹ = 1`. Establish `h` using `congrArg c D.mul_inv`. Rewrite `h` using `[map_mul, map_one, hD, map_sub, hc]`.

Conclude with `h`. Establish `hw : ω * ↑D⁻¹ + c (ω * ↑D⁻¹) = 1`. Establish `hinv : (↑D⁻¹ : R) * (ω - c ω) = 1` using `by rw [← hD]; exact D.inv_mul`. Rewrite using `[map_mul]`. Take the linear combination `(1 - ω * ↑D⁻¹) * hcD - ω * c ↑D⁻¹ * hinv`.

Establish `hI' : I ≤ I.comap c` using `fun x hx => hI x hx`. Set `cb : R ⧸ I →+* R ⧸ I` to `Ideal.quotientMap I c hI'`. Establish `hmk : ∀ x, cb (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c x)` using `fun x => Ideal.quotientMap_mk`. Establish `hcb : ∀ x, cb (cb x) = x`. Introduce `x`.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hmk, hmk, hc]`. Establish `hunit : IsUnit (Ideal.Quotient.mk I ω - cb (Ideal.Quotient.mk I ω))`. Rewrite using `[hmk, ← map_sub, ← hD]`. Conclude with `D.isUnit.map _`.

Take `⟨xb, hxb⟩` from `GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj (R ⧸ I) cb hcb ⟨_, hunit⟩ (Ideal.Quotient.mk I u) (by rw [hmk, hcu]) (hu.map _)`. Take `⟨x₀, rfl⟩` from `Ideal.Quotient.mk_surjective xb`. Rewrite `hxb` using `[hmk, ← map_mul]`. Establish `hmem : x₀ * c x₀ - u ∈ I` using `Ideal.Quotient.eq.mp hxb`. Take `⟨U, rfl⟩` from `hu`.

Establish `hcU : c ↑U⁻¹ = ↑U⁻¹`. Establish `h : (U : R) * c ↑U⁻¹ = 1`. Rewrite using `[← hcu, ← map_mul, U.mul_inv, map_one]`. Conclude with `(Units.inv_eq_of_mul_eq_one_right h).symm`. Take `⟨a, ha⟩ : ∃ a, a = (x₀ * c x₀ - ↑U) * ↑U⁻¹` from `⟨_, rfl⟩`.

Establish `haI : a ∈ I` using `ha ▸ I.mul_mem_right _ hmem`. Establish `hca : c a = a`. Rewrite using `[ha]`. Simplify using `only [map_mul, map_sub, hc, hcu, hcU]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨V, hV⟩` from `(Ideal.mem_jacobson_bot.mp (HenselianRing.jac haI)) 1`. Establish `hcV : c ↑V = ↑V` using `by rw [hV, map_add, map_mul, map_one, hca]`. Establish `hcVi : c ↑V⁻¹ = ↑V⁻¹`. Establish `h : (V : R) * c ↑V⁻¹ = 1`. Rewrite using `[← hcV, ← map_mul, V.mul_inv, map_one]`.

Conclude with `(Units.inv_eq_of_mul_eq_one_right h).symm`. Establish `heI : (↑V⁻¹ : R) - 1 ∈ I`. Establish `h : (↑V⁻¹ : R) - 1 = -(↑V⁻¹ * a)`. Take the linear combination `(-(↑V⁻¹ : R)) * hV + V.inv_mul`. Rewrite using `[h]`.

Conclude with `I.neg_mem (I.mul_mem_left _ haI)`. Take `⟨y, hy⟩` from `exists_norm_eq_one_add I c hc hI hw heI (by rw [map_sub, hcVi, map_one])`. Establish `hvU : x₀ * c x₀ = ↑U * ↑V`. Rewrite using `[hV, ha]`. Take the linear combination `(-(x₀ * c x₀ - ↑U)) * U.mul_inv`.

Use `⟨x₀ * y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Take the linear combination `(x₀ * c x₀) * hy + (↑V⁻¹ : R) * hvU + (↑U : R) * V.mul_inv`.
-/
theorem exists_norm_eq : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I]
    [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) →
    (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro R _ I _ _ c hc hI hω u hcu hu
  obtain ⟨ω, D, hD⟩ := hω
  have hcD : (c ω - ω) * c ↑D⁻¹ = 1 := by
    have h := congrArg c D.mul_inv
    rw [map_mul, map_one, hD, map_sub, hc] at h
    exact h
  have hw : ω * ↑D⁻¹ + c (ω * ↑D⁻¹) = 1 := by
    have hinv : (↑D⁻¹ : R) * (ω - c ω) = 1 := by rw [← hD]; exact D.inv_mul
    rw [map_mul]
    linear_combination (1 - ω * ↑D⁻¹) * hcD - ω * c ↑D⁻¹ * hinv
  have hI' : I ≤ I.comap c := fun x hx => hI x hx
  let cb : R ⧸ I →+* R ⧸ I := Ideal.quotientMap I c hI'
  have hmk : ∀ x, cb (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (c x) :=
    fun x => Ideal.quotientMap_mk
  have hcb : ∀ x, cb (cb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hmk, hmk, hc]
  have hunit : IsUnit (Ideal.Quotient.mk I ω - cb (Ideal.Quotient.mk I ω)) := by
    rw [hmk, ← map_sub, ← hD]
    exact D.isUnit.map _
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj (R ⧸ I) cb hcb ⟨_, hunit⟩ (Ideal.Quotient.mk I u)
    (by rw [hmk, hcu]) (hu.map _)
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective xb
  rw [hmk, ← map_mul] at hxb
  have hmem : x₀ * c x₀ - u ∈ I := Ideal.Quotient.eq.mp hxb
  obtain ⟨U, rfl⟩ := hu
  have hcU : c ↑U⁻¹ = ↑U⁻¹ := by
    have h : (U : R) * c ↑U⁻¹ = 1 := by
      rw [← hcu, ← map_mul, U.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  obtain ⟨a, ha⟩ : ∃ a, a = (x₀ * c x₀ - ↑U) * ↑U⁻¹ := ⟨_, rfl⟩
  have haI : a ∈ I := ha ▸ I.mul_mem_right _ hmem
  have hca : c a = a := by
    rw [ha]
    simp only [map_mul, map_sub, hc, hcu, hcU]
    ring
  obtain ⟨V, hV⟩ := (Ideal.mem_jacobson_bot.mp (HenselianRing.jac haI)) 1
  have hcV : c ↑V = ↑V := by rw [hV, map_add, map_mul, map_one, hca]
  have hcVi : c ↑V⁻¹ = ↑V⁻¹ := by
    have h : (V : R) * c ↑V⁻¹ = 1 := by
      rw [← hcV, ← map_mul, V.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h).symm
  have heI : (↑V⁻¹ : R) - 1 ∈ I := by
    have h : (↑V⁻¹ : R) - 1 = -(↑V⁻¹ * a) := by
      linear_combination (-(↑V⁻¹ : R)) * hV + V.inv_mul
    rw [h]
    exact I.neg_mem (I.mul_mem_left _ haI)
  obtain ⟨y, hy⟩ := exists_norm_eq_one_add I c hc hI hw heI (by rw [map_sub, hcVi, map_one])
  have hvU : x₀ * c x₀ = ↑U * ↑V := by
    rw [hV, ha]
    linear_combination (-(x₀ * c x₀ - ↑U)) * U.mul_inv
  refine ⟨x₀ * y, ?_⟩
  rw [map_mul]
  linear_combination (x₀ * c x₀) * hy + (↑V⁻¹ : R) * hvU + (↑U : R) * V.mul_inv

end GlobalTheory.HenselianNorm
