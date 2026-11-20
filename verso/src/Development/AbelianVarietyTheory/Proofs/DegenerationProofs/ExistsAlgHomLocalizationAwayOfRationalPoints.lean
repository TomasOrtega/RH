import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Take `⟨n, q, hq⟩` from `IsLocalization.Away.surj D b`. Establish `hq0 : q * D = 0`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_zero]`.

Distinguish the cases in `ht : D.eval t = 0`. Rewrite using `[ht, mul_zero]`. Establish `hu : IsUnit (Polynomial.evalRingHom t D)` using `isUnit_iff_ne_zero.mpr ht`. Establish `he : ∀ q, (IsLocalization.Away.lift (S` using `Localization.Away D) D hu) (algebraMap (Polynomial k) _ q) = q.eval t := fun q => IsLocalization.Away.lift_eq D hu q`. Establish `h0` using `h t ht _ he`.

Establish `h1` using `congrArg (IsLocalization.Away.lift (S := Localization.Away D) D hu) hq`. Rewrite `h1` using `[map_mul, h0, zero_mul, he]`. Rewrite using `[← h1, zero_mul]`. Establish `hq1 : q = 0` using `(mul_eq_zero.mp hq0).resolve_right hD`. Rewrite `hq` using `[hq1, map_zero]`.

Conclude with `((IsLocalization.Away.algebraMap_isUnit D).pow n).mul_left_eq_zero.mp hq`.
-/
theorem localizationAway_eq_zero_of_forall_eval {k : Type} [Field k] [Infinite k]
    (D : Polynomial k) (hD : D ≠ 0) (b : Localization.Away D)
    (h : ∀ t, D.eval t ≠ 0 → ∀ e : Localization.Away D →+* k,
      (∀ q, e (algebraMap (Polynomial k) _ q) = q.eval t) → e b = 0) : b = 0 := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj D b
  have hq0 : q * D = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : D.eval t = 0
    · rw [ht, mul_zero]
    · have hu : IsUnit (Polynomial.evalRingHom t D) := isUnit_iff_ne_zero.mpr ht
      have he : ∀ q, (IsLocalization.Away.lift (S := Localization.Away D) D hu)
          (algebraMap (Polynomial k) _ q) = q.eval t := fun q =>
        IsLocalization.Away.lift_eq D hu q
      have h0 := h t ht _ he
      have h1 := congrArg (IsLocalization.Away.lift (S := Localization.Away D) D hu) hq
      rw [map_mul, h0, zero_mul, he] at h1
      rw [← h1, zero_mul]
  have hq1 : q = 0 := (mul_eq_zero.mp hq0).resolve_right hD
  rw [hq1, map_zero] at hq
  exact ((IsLocalization.Away.algebraMap_isUnit D).pow n).mul_left_eq_zero.mp hq

/- English proof (translation)
Introduce `k _ _ A _ _ r f Pd P ψ hf hPd hψ`. Establish `hD : (Polynomial.X * Pd : Polynomial k) ≠ 0` using `mul_ne_zero Polynomial.X_ne_zero hPd`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : Localization.Away (Polynomial.X * Pd), u * algebraMap (Polynomial k) _ Pd = 1 := by`. Establish `h` using `IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.X * Pd)) (Polynomial.X * Pd)`. Rewrite `h` using `[map_mul]`.

Conclude with `(isUnit_of_mul_isUnit_right h).exists_left_inv`. Set `Θ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away (Polynomial.X * Pd)` to `MvPolynomial.aeval fun i => algebraMap (Polynomial k) _ (P i) * u`. Establish `hsurj : Function.Surjective (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A)`. Rewrite using `[← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hf]`. Establish `hker : ∀ p, MvPolynomial.aeval f p = 0 → Θ p = 0`.

Introduce `p hp`. Apply `localizationAway_eq_zero_of_forall_eval _ hD` to reduce the goal to its premises. Introduce `t ht e he`. Rewrite `ht` using `[Polynomial.eval_mul, Polynomial.eval_X]`. Establish `ht0 : t ≠ 0` using `left_ne_zero_of_mul ht`.

Establish `ht1 : Pd.eval t ≠ 0` using `right_ne_zero_of_mul ht`. Establish `key : ∀ p, e (Θ p) = ψ t (MvPolynomial.aeval f p)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`.

Rewrite using `[MvPolynomial.algHom_C, MvPolynomial.algHom_C, AlgHom.commutes, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.X * Pd)), he]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, hp]`.

Use `congr 1`. Establish `h1` using `congrArg e hu`. Rewrite `h1` using `[map_mul, he, map_one]`. Simplify using `only [Θ, MvPolynomial.aeval_X, map_mul, he]`. Rewrite using `[← hψ t ht0 ht1 i, mul_assoc, mul_comm (Pd.eval t), h1, mul_one]`.

Rewrite using `[key, hp, map_zero]`. Establish `hle : RingHom.ker (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A).toRingHom ≤ RingHom.ker Θ.toRingHom` using `fun p hp => hker p hp`. Use `⟨AlgHom.liftOfSurjective _ hsurj Θ hle, fun i => ?_⟩` and prove the remaining obligations. Establish `h2 : f i = MvPolynomial.aeval f (MvPolynomial.X i : MvPolynomial (Fin r) k)` using `by simp`. Rewrite using `[h2]`.

Use `erw [AlgHom.liftOfSurjective_apply]`. Simplify using `only [Θ, MvPolynomial.aeval_X]`. Rewrite using `[mul_assoc, hu, mul_one]`.
-/
theorem exists_algHom_localizationAway_of_rational_points :
    ∀ (k : Type) [Field k] [Infinite k] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → Pd ≠ 0 → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → ∃ χ : A →ₐ[k] Localization.Away (Polynomial.X * Pd), ∀ i, χ (f i) * algebraMap (Polynomial k) _ Pd = algebraMap (Polynomial k) _ (P i) := by
  intro k _ _ A _ _ r f Pd P ψ hf hPd hψ
  have hD : (Polynomial.X * Pd : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  obtain ⟨u, hu⟩ : ∃ u : Localization.Away (Polynomial.X * Pd),
      u * algebraMap (Polynomial k) _ Pd = 1 := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)
    rw [map_mul] at h
    exact (isUnit_of_mul_isUnit_right h).exists_left_inv
  let Θ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away (Polynomial.X * Pd) :=
    MvPolynomial.aeval fun i => algebraMap (Polynomial k) _ (P i) * u
  have hsurj : Function.Surjective (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hf]
  have hker : ∀ p, MvPolynomial.aeval f p = 0 → Θ p = 0 := by
    intro p hp
    apply localizationAway_eq_zero_of_forall_eval _ hD
    intro t ht e he
    rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
    have ht0 : t ≠ 0 := left_ne_zero_of_mul ht
    have ht1 : Pd.eval t ≠ 0 := right_ne_zero_of_mul ht
    have key : ∀ p, e (Θ p) = ψ t (MvPolynomial.aeval f p) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C, AlgHom.commutes,
          IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.X * Pd)),
          he]
        simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp =>
        rw [map_mul, map_mul, map_mul, map_mul, hp]
        congr 1
        have h1 := congrArg e hu
        rw [map_mul, he, map_one] at h1
        simp only [Θ, MvPolynomial.aeval_X, map_mul, he]
        rw [← hψ t ht0 ht1 i, mul_assoc, mul_comm (Pd.eval t), h1, mul_one]
    rw [key, hp, map_zero]
  have hle : RingHom.ker (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A).toRingHom ≤
      RingHom.ker Θ.toRingHom := fun p hp => hker p hp
  refine ⟨AlgHom.liftOfSurjective _ hsurj Θ hle, fun i => ?_⟩
  have h2 : f i = MvPolynomial.aeval f (MvPolynomial.X i : MvPolynomial (Fin r) k) := by simp
  rw [h2]
  erw [AlgHom.liftOfSurjective_apply]
  simp only [Θ, MvPolynomial.aeval_X]
  rw [mul_assoc, hu, mul_one]

end GlobalTheory
