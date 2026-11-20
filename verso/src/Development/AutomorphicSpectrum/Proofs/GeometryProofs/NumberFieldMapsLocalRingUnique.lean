import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.TwoMaps

open Polynomial

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Establish `hsep : (minpoly ℚ a).Separable` using `Algebra.IsSeparable.isSeparable ℚ a`. Take `⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K)` from `⟨_, rfl⟩`. Establish `hpa : p.eval a = 0`. Rewrite using `[hp, eval_map_algebraMap]`.

Conclude with `minpoly.aeval ℚ a`. Establish `hpd : p.derivative.eval a ≠ 0`. Rewrite using `[hp, derivative_map, eval_map_algebraMap]`. Conclude with `hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)`. Establish `hst : p.map s = p.map t`.

Rewrite using `[hp, Polynomial.map_map, Polynomial.map_map]`. Use `congr 1`. Conclude with `RingHom.ext_rat _ _`. Establish `hx : (p.map s).eval (s a) = 0`. Rewrite using `[eval_map, eval₂_at_apply, hpa, map_zero]`.

Establish `hy : (p.map s).eval (t a) = 0`. Rewrite using `[hst, eval_map, eval₂_at_apply, hpa, map_zero]`. Establish `hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a)`. Rewrite using `[derivative_map, eval_map, eval₂_at_apply]`. Establish `hunit : IsUnit ((p.map s).derivative.eval (s a))`.

Rewrite using `[hdx]`. Conclude with `(IsUnit.mk0 _ hpd).map s`. Take `⟨k, hk⟩` from `binomExpansion (p.map s) (s a) (t a - s a)`. Establish `hd : ¬ IsUnit (t a - s a)`. Introduce `hu`.

Establish `h0 : π (t a - s a) = 0`. Use `RingHom.congr_fun h a` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[map_sub, this, sub_self]`. Conclude with `(hu.map π).ne_zero h0`.

Establish `hkd : ¬ IsUnit (-(k * (t a - s a)))`. Rewrite using `[IsUnit.neg_iff]`. Conclude with `fun hu => hd (isUnit_of_mul_isUnit_right hu)`. Establish `hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a))`. Assume the negation of the conclusion as `hc`.

Establish `hsum` using `IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a)) (b := -(k * (t a - s a))) hc hkd`. Apply `hsum` to reduce the goal to its premises. Simplify using `using hunit`. Establish `hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0`. Establish `e : s a + (t a - s a) = t a` using `by ring`.

Rewrite `hk` using `[e, hy, hx]`. Take the linear combination `-hk`. Establish `hz : t a - s a = 0`. Simplify using `using (hu2.mul_left_eq_zero).1 hmul`. Conclude with `(sub_eq_zero.1 hz).symm`.
-/
theorem ringHom_eq_of_comp_eq (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B]
    [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B)
    (h : π.comp s = π.comp t) : s = t := by
  refine RingHom.ext fun a => ?_
  have hsep : (minpoly ℚ a).Separable := Algebra.IsSeparable.isSeparable ℚ a
  obtain ⟨p, hp⟩ : ∃ p : K[X], p = (minpoly ℚ a).map (algebraMap ℚ K) := ⟨_, rfl⟩
  have hpa : p.eval a = 0 := by
    rw [hp, eval_map_algebraMap]
    exact minpoly.aeval ℚ a
  have hpd : p.derivative.eval a ≠ 0 := by
    rw [hp, derivative_map, eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ a)
  have hst : p.map s = p.map t := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hx : (p.map s).eval (s a) = 0 := by
    rw [eval_map, eval₂_at_apply, hpa, map_zero]
  have hy : (p.map s).eval (t a) = 0 := by
    rw [hst, eval_map, eval₂_at_apply, hpa, map_zero]
  have hdx : (p.map s).derivative.eval (s a) = s (p.derivative.eval a) := by
    rw [derivative_map, eval_map, eval₂_at_apply]
  have hunit : IsUnit ((p.map s).derivative.eval (s a)) := by
    rw [hdx]
    exact (IsUnit.mk0 _ hpd).map s
  obtain ⟨k, hk⟩ := binomExpansion (p.map s) (s a) (t a - s a)
  have hd : ¬ IsUnit (t a - s a) := by
    intro hu
    have h0 : π (t a - s a) = 0 := by
      have := RingHom.congr_fun h a
      simp only [RingHom.comp_apply] at this
      rw [map_sub, this, sub_self]
    exact (hu.map π).ne_zero h0
  have hkd : ¬ IsUnit (-(k * (t a - s a))) := by
    rw [IsUnit.neg_iff]
    exact fun hu => hd (isUnit_of_mul_isUnit_right hu)
  have hu2 : IsUnit ((p.map s).derivative.eval (s a) + k * (t a - s a)) := by
    by_contra hc
    have hsum := IsLocalRing.nonunits_add (R := B) (a := (p.map s).derivative.eval (s a) + k * (t a - s a))
      (b := -(k * (t a - s a))) hc hkd
    apply hsum
    simpa using hunit
  have hmul : (t a - s a) * ((p.map s).derivative.eval (s a) + k * (t a - s a)) = 0 := by
    have e : s a + (t a - s a) = t a := by ring
    rw [e, hy, hx] at hk
    linear_combination -hk
  have hz : t a - s a = 0 := by
    simpa using (hu2.mul_left_eq_zero).1 hmul
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.CompanionTheory.Ggeo.TwoMaps
