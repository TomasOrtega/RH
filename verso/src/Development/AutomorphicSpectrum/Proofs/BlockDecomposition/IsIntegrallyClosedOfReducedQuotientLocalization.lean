import Mathlib

namespace GlobalTheory.CompanionTheory.IntClosedAway

open Polynomial

/- English proof (translation)
Take `⟨p, hp, hpz⟩` from `hz`. Establish `hinj` using `IsFractionRing.injective A K`. Establish `h1 : (p.scaleRoots t).eval a = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]`.

Establish `h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree`. Establish `ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)`. Use extensionality with `i`. Rewrite using `[coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]`. Break down `lt_trichotomy i p.natDegree with hi | hi | hi` into its components or cases.

Rewrite using `[if_neg hi.ne, zero_pow (by omega), mul_zero]`. Substitute `hi` using the available equality. Simplify using `[hp.coeff_natDegree]`. Rewrite using `[if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]`. Establish `h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0`.

Establish `h4` using `congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1`. Rewrite `h4` using `[map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2]`. Simplify using `using h4`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)`.
-/
theorem mem_span_of_eq_mul_integral {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (t a : A) (hred : IsReduced (A ⧸ Ideal.span {t})) (z : K)
    (hz : IsIntegral A z) (h : algebraMap A K a = algebraMap A K t * z) :
    a ∈ Ideal.span {t} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hinj := IsFractionRing.injective A K
  have h1 : (p.scaleRoots t).eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]
  have h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree := by
    have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    ext i
    rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, zero_pow (by omega), mul_zero]
    · subst hi
      simp [hp.coeff_natDegree]
    · rw [if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  have h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0 := by
    have h4 := congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2] at h4
    simpa using h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)

/- English proof (translation)
Introduce `A _ _ t ht hred hcl`. Establish `hle : Submonoid.powers t ≤ nonZeroDivisors A` using `powers_le_nonZeroDivisors_of_noZeroDivisors ht`. Use `haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle`. Set `K` to `FractionRing A`. Use `letI : Algebra (Localization.Away t) K := (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K) (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra`.

Use `haveI : IsScalarTower A (Localization.Away t) K := IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm`. Use `haveI : IsFractionRing (Localization.Away t) K := IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle`. Rewrite using `[isIntegrallyClosed_iff K]`. Introduce `x hx`. Establish `hxB : IsIntegral (Localization.Away t) x` using `hx.tower_top`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hxB`. Take `⟨n, a, hna⟩` from `IsLocalization.Away.surj t y`. Establish `hxa : algebraMap A K a = x * algebraMap A K t ^ n`. Establish `h5` using `congrArg (algebraMap (Localization.Away t) K) hna`. Rewrite `h5` using `[map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K]`.

Conclude with `h5.symm`. Establish `ht' : algebraMap A K t ≠ 0`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht`. Use `clear hna`. Proceed by induction on `n generalizing a with`.

Consider the case `zero => exact ⟨a, by simpa using hxa⟩`. Consider the case `succ n ih`. Establish `hz : IsIntegral A (x * algebraMap A K t ^ n)` using `hx.mul (isIntegral_algebraMap.pow n)`. Establish `hmem : a ∈ Ideal.span {t}` using `mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp hmem`.

Use `ih b (mul_left_injective₀ ht' ?_)` and prove the remaining obligations. Simplify using `only [map_mul] at hxa`. Simplify using `only [hxa]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isIntegrallyClosed_of_away :
    ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) →
      IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  intro A _ _ t ht hred hcl
  have hle : Submonoid.powers t ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  let K := FractionRing A
  letI : Algebra (Localization.Away t) K :=
    (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K)
      (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra
  haveI : IsScalarTower A (Localization.Away t) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  haveI : IsFractionRing (Localization.Away t) K :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hxB : IsIntegral (Localization.Away t) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj t y
  have hxa : algebraMap A K a = x * algebraMap A K t ^ n := by
    have h5 := congrArg (algebraMap (Localization.Away t) K) hna
    rw [map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K,
      ← IsScalarTower.algebraMap_apply A (Localization.Away t) K] at h5
    exact h5.symm
  have ht' : algebraMap A K t ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht
  clear hna
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using hxa⟩
  | succ n ih =>
    have hz : IsIntegral A (x * algebraMap A K t ^ n) := hx.mul (isIntegral_algebraMap.pow n)
    have hmem : a ∈ Ideal.span {t} :=
      mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih b (mul_left_injective₀ ht' ?_)
    simp only [map_mul] at hxa
    simp only [hxa]
    ring

end GlobalTheory.CompanionTheory.IntClosedAway
